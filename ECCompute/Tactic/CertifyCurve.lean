/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.MainTheorem
import ECCompute.Soundness.Torsion
import Mathlib.Lean.Expr.Rat

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE W ρ`, where `W` is a Weierstrass curve over `ℚ` whose
coefficients are integers. It reads the coefficients and rank from the goal (so the curve must be
`unfold`ed to a `WeierstrassCurve` literal first) and the generating points and descent labels from
two data files, computes the descent-character matrix and its `𝔽₂` inverse, bundles the
required checks into a `Certificate.Valid`, and applies `hasRankGE_of_certificate`.

Each data file has one entry per line. A points file has `x y`, with each coordinate either an
integer or a reduced fraction `a/b`; a labels file has `p θ`, the descent character at the root `θ`
of the 2-division cubic mod `p`.

```
theorem hasRankGE_example : HasRankGE curveExample 29 := by
  unfold curveExample exampleA₄ exampleA₆   -- expose the `WeierstrassCurve` literal in the goal
  certify_curve torsion 67 "data/example.txt" "data/example-labels.txt"
```
-/

/-!
## Evaluator-side helpers

These functions reproduce the descent character and the `𝔽₂` matrix inverse using plain
`Int`/`Nat` arithmetic (the Legendre symbol via quadratic reciprocity), written for the
compiler/interpreter. The `certify_curve` elaborator calls them to produce a certificate's
character matrix `B` and its inverse `M`.
-/

namespace ECCompute.CertifyEval

/-- The Jacobi symbol `(a | n)` for odd `n`, by quadratic reciprocity. For prime `n` this is
the Legendre symbol. Returns `0`, `1`, or `-1`. -/
partial def jacobi (a : Int) (n : Nat) : Int := Id.run do
  let mut a := ((a % (n : Int)) + n).toNat % n
  let mut n := n
  let mut acc : Int := 1
  while a != 0 do
    while a % 2 == 0 do
      a := a / 2
      if n % 8 == 3 || n % 8 == 5 then acc := -acc
    let t := a; a := n; n := t
    if a % 4 == 3 && n % 4 == 3 then acc := -acc
    a := a % n
  return if n == 1 then acc else 0

/-- Evaluator-side value of the descent character `λ_{p,θ}` on a point whose `x`-coordinate is
`xnum / xden`, mirroring `ECCompute.lambdaK` (`true` = nontrivial). `a₂ a₄` are the
short-model coefficients; the cubic's constant term `a₆` does not enter the character. -/
def lambdaEval (a₂ a₄ : Int) (p : Nat) (θ xnum : Int) (xden : Nat) : Bool :=
  if (xden : Int) % (p : Int) == 0 then false
  else
    let α := (xnum - θ * (xden : Int)) % (p : Int)
    -- tangent case `x.num ≡ θ·x.den`: evaluate at the derivative `3θ² + 2a₂θ + a₄`
    let a := if α == 0 then 3 * θ ^ 2 + 2 * a₂ * θ + a₄ else α
    jacobi a p != 1

/-- Pack booleans `p 0, …, p (n-1)` into a `Nat` bitmask: bit `j` set iff `p j`. -/
def bitmaskOf (n : Nat) (p : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc j ↦ if p j then acc ||| (1 <<< j) else acc) 0

/-- The descent-character matrix `B` as `Nat` row bitmasks: row `i` has bit `j` set iff the
character of label `ls[j]` on the point with `x`-coordinate `xs[i] = (num, den)` is nontrivial. -/
def computeB (a₂ a₄ : Int) (xs : List (Int × Nat)) (ls : List (Nat × Int)) : List Nat :=
  xs.map fun x ↦
    bitmaskOf ls.length (fun j ↦ let l := ls[j]!; lambdaEval a₂ a₄ l.1 l.2 x.1 x.2)

/-- The quadratic-residue bitmask mod an odd prime `p`: bit `a` set iff `a` is a nonzero square mod
`p`, computed as the OR of `1 <<< (j² % p)` for `j = 1 .. (p-1)/2`. Matches `ECCompute.qrMask`. -/
def qrMaskNat (p : Nat) : Nat :=
  (List.range ((p - 1) / 2)).foldl (fun acc k ↦ acc ||| (1 <<< ((k + 1) * (k + 1) % p))) 0

/-- Invert an `n × n` matrix over `𝔽₂` given as `Nat` row bitmasks, returning the inverse in the
column-bitmask convention of `F2Invert.toMatCols` (so it feeds `checkInv` as `M`). Returns
`none` if the matrix is singular. -/
def invF2 (B : Array Nat) (n : Nat) : Option (List Nat) := Id.run do
  let mut a := B
  let mut inv : Array Nat := (Array.range n).map (fun i ↦ (1 <<< i : Nat))
  for col in [0:n] do
    let mut piv : Option Nat := none
    for r in [col:n] do
      if a[r]!.testBit col then
        piv := some r
        break
    match piv with
    | none => return none
    | some r =>
      if r != col then
        let ta := a[col]!; a := a.set! col a[r]!; a := a.set! r ta
        let ti := inv[col]!; inv := inv.set! col inv[r]!; inv := inv.set! r ti
      for r2 in [0:n] do
        if r2 != col && a[r2]!.testBit col then
          a := a.set! r2 (a[r2]! ^^^ a[col]!)
          inv := inv.set! r2 (inv[r2]! ^^^ inv[col]!)
  return some <| (List.range n).map fun k ↦
    bitmaskOf n (fun j ↦ inv[j]!.testBit k)

end ECCompute.CertifyEval

open Lean Elab Tactic Meta

namespace ECCompute

/-- Two Weierstrass curves over `ℚ` are equal when their five coefficient `BEq` checks all hold.
The tactic uses this to prove the model equality from five `reflBoolTrue` witnesses. -/
public theorem _root_.WeierstrassCurve.ext_of_beq {W W' : WeierstrassCurve ℚ}
    (h₁ : W.a₁ == W'.a₁) (h₂ : W.a₂ == W'.a₂) (h₃ : W.a₃ == W'.a₃)
    (h₄ : W.a₄ == W'.a₄) (h₆ : W.a₆ == W'.a₆) : W = W' :=
  WeierstrassCurve.ext (eq_of_beq h₁) (eq_of_beq h₂) (eq_of_beq h₃) (eq_of_beq h₄) (eq_of_beq h₆)

/-- Extract a literal from `e`: try `parse` on the raw term, then on its `whnf`, then `fallback`.
`kind` names the expected type in the error. -/
def getLitE {α} (kind : String) (parse : Expr → Option α)
    (fallback : Expr → MetaM (Option α)) (e : Expr) : MetaM α := do
  if let some n := parse (← whnfR e) then return n
  let e ← whnf e
  if let some n := parse e then return n
  if let some n ← fallback e then return n
  throwError "certify_curve: expected a `{kind}` literal, got{indentExpr e}"

/-- Extract the `Nat` value of a numeral `Expr`. -/
def getNatE (e : Expr) : MetaM Nat := getLitE "Nat" (·.nat?) getNatValue? e

/-- ASCII-trim `s`, returning a `String`. -/
def strTrim (s : String) : String := s.trimAscii.toString

/-- Parse a coordinate string `"a"` or `"a/b"` into a *reduced* `(numerator, denominator)`. -/
def parseCoord (s : String) : Int × Nat :=
  match (strTrim s).splitOn "/" with
  | [a, b] =>
    let num := (strTrim a).toInt!
    let den := (strTrim b).toNat!
    let g := Nat.gcd num.natAbs den
    if g == 0 then (num, den) else (num / (g : Int), den / g)
  | _ => ((strTrim s).toInt!, 1)

/-- Split a whitespace-trimmed line on spaces into its nonempty fields. -/
def fields (line : String) : List String :=
  ((strTrim line).splitOn " ").filter (· ≠ "")

/-- Parse one line `"x y"` of a points file into `(x.num, x.den, y.num, y.den)`. -/
def parseLine (line : String) : Option (Int × Nat × Int × Nat) :=
  match fields line with
  | [xs, ys] => let (xn, xd) := parseCoord xs; let (yn, yd) := parseCoord ys; some (xn, xd, yn, yd)
  | _ => none

/-- `ℚ` Expr for `num / den` (reduced) via `mkRat`, whose reduction the kernel performs by
computation, leaving the emitted term a bare numerator/denominator pair. -/
def coordExpr (num : Int) (den : Nat) : Expr :=
  mkApp2 (mkConst ``mkRat) (toExpr num) (toExpr den)

/-- Parse one line `"p θ"` of a labels file into the descent column `(p, θ)`. -/
def parseLabel (line : String) : Option (Nat × Int) :=
  match fields line with
  | [p, t] => some ((strTrim p).toNat!, (strTrim t).toInt!)
  | _ => none

/-- An integer literal argument: a numeral `n`, or `(-n)` for a negative. -/
declare_syntax_cat intLit
syntax num : intLit
syntax "(" "-" num ")" : intLit

/-- Read the `Int` value of an `intLit`. -/
def getIntLit : TSyntax `intLit → MetaM Int
  | `(intLit| $n:num) => return (n.getNat : Int)
  | `(intLit| (-$n:num)) => return -(n.getNat : Int)
  | _ => throwError "certify_curve: expected an integer literal"

/-- Syntax of the `certify_curve` tactic (see the module docstring). There are three torsion forms.
`torsion ℓ` handles `t = 0` via a witness prime `ℓ` at which the `2`-division cubic has no root.
`oneTorsion` handles `t = 1`, taking a short-model root `R` and a prime `ℓ` where the quadratic
cofactor has no root. `fullTorsion` handles `t = 2` (e.g. square-discriminant curves) through the
universal bound. -/
syntax "certify_curve" " torsion " num str str : tactic

syntax "certify_curve" " fullTorsion " str str : tactic

syntax "certify_curve" " oneTorsion " intLit num str str : tactic

/-- Extract the integer value of an integer-valued `ℚ` literal `Expr`: an `OfNat` numeral, its
negation, or an `Int.cast` of an `ℤ` literal. Errors if the coefficient is not an integer. -/
def getRatIntE (e : Expr) : MetaM Int := do
  let checkInt (q : Rat) : MetaM Int := do
    if q.den == 1 then return q.num
    throwError "certify_curve: curve coefficient is not an integer{indentExpr e}"
  if let some q := e.rat? then return ← checkInt q          -- `OfNat` / `Neg (OfNat …)`
  if e.isAppOfArity ``Int.cast 3 then                       -- `((n : ℤ) : ℚ)` with `n` a literal
    if let some n := e.appArg!.int? then return n
  if let some q := (← whnfR e).rat? then return ← checkInt q
  if let some q := (← whnf e).rat? then return ← checkInt q  -- unfold abbreviations
  throwError "certify_curve: expected an integer-valued rational coefficient, got{indentExpr e}"

/-- Read `HasRankGE W ρ` off `goal`, where `W` reduces to a `WeierstrassCurve.mk` literal with
integer-valued rational coefficients. Returns the rank `ρ`, the original curve `Expr` `W`, and the
five integer coefficient values. -/
def readGoal (goal : MVarId) :
    MetaM (Nat × Expr × Int × Int × Int × Int × Int) := do
  let (``HasRankGE, #[curveE, ρE]) := (← goal.getType).getAppFnArgs
    | throwError "certify_curve: goal must be `HasRankGE _ _`"
  let (``WeierstrassCurve.mk, #[_, q1E, q2E, q3E, q4E, q6E]) := (← whnf curveE).getAppFnArgs
    | throwError "certify_curve: the curve must reduce to a `WeierstrassCurve` literal; \
        `unfold` your curve definition and its coefficient abbreviations first"
  return (← getNatE ρE, curveE,
    ← getRatIntE q1E, ← getRatIntE q2E, ← getRatIntE q3E, ← getRatIntE q4E, ← getRatIntE q6E)

/-- Read `path`, drop blank lines, and parse each remaining line with `parse`. `what` names the
line kind in the error message. -/
def readEntries {α} (what : String) (parse : String → Option α) (path : String) :
    MetaM (Array α) := do
  ((← IO.FS.readFile path).splitOn "\n").toArray.filterMapM fun l ↦ do
    if (strTrim l).isEmpty then return none
    match parse l with
    | some a => return some a
    | none => throwError "certify_curve: malformed {what} line: {l}"

/-- Read and parse the points file (`x y` per line) and labels file (`p θ`), checking each has
`ρ` entries. -/
def readData (path lpath : String) (ρ : Nat) :
    MetaM (Array (Int × Nat × Int × Nat) × Array (Nat × Int)) := do
  let pts ← readEntries "points" parseLine path
  let ls ← readEntries "labels" parseLabel lpath
  if pts.size ≠ ρ then
    throwError "certify_curve: points file has {pts.size} points but the goal rank is {ρ}"
  if ls.size ≠ ρ then
    throwError "certify_curve: labels file has {ls.size} labels but the goal rank is {ρ}"
  return (pts, ls)

/-- The descent-character matrix over the short model and its 𝔽₂ inverse (a pure computation). -/
def buildMats (sA2 sA4 : Int) (xs : List (Int × Nat)) (ls : List (Nat × Int)) (ρ : Nat) :
    MetaM (List Nat × List Nat) := do
  let B := CertifyEval.computeB sA2 sA4 xs ls
  let some M := CertifyEval.invF2 B.toArray ρ
    | throwError "certify_curve: the descent-character matrix is singular over 𝔽₂"
  return (B, M)

/-- The pair type `ℚ × ℚ` as an `Expr`. -/
def ratPairTy : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Rat) (mkConst ``Rat)

/-- The short-model coefficient Exprs `(a₂, a₄, a₆)` built from the integer coefficient Exprs
`a₁…a₆` via `IntegralScaling.intShortA₂/₄/₆`. -/
def shortCoeffExprs (a1E a2E a3E a4E a6E : Expr) : Expr × Expr × Expr :=
  (mkApp2 (mkConst ``IntegralScaling.intShortA₂) a1E a2E,
    mkApp3 (mkConst ``IntegralScaling.intShortA₄) a1E a3E a4E,
    mkApp2 (mkConst ``IntegralScaling.intShortA₆) a3E a6E)

/-- Build the `Certificate` Expr directly with the `Meta` API (no `Syntax`/`quote`/`delab`). -/
def mkCertExpr (ρ : Nat) (pts : Array (Int × Nat × Int × Nat)) (ls : Array (Nat × Int))
    (B M : List Nat) (t tp : Nat) (a1E a2E a3E a4E a6E : Expr) : MetaM Expr := do
  let ratTy := mkConst ``Rat
  let pairTy := ratPairTy
  let ptExprs := pts.toList.map fun (xn, xd, yn, yd) ↦
    mkAppN (mkConst ``Prod.mk [Level.zero, Level.zero])
      #[ratTy, ratTy, coordExpr xn xd, coordExpr yn yd]
  let pointsE ← mkListLit pairTy ptExprs
  let (sA2E, sA4E, sA6E) := shortCoeffExprs a1E a2E a3E a4E a6E
  let q := ls.toList.map fun l ↦ CertifyEval.qrMaskNat l.1
  return mkAppN (mkConst ``Certificate.mk)
    #[sA2E, sA4E, sA6E, toExpr ρ, pointsE,
      toExpr ls.toList, toExpr B, toExpr M, toExpr q, toExpr t, toExpr tp]

/-- A `List.length` equality from a kernel-reducible `BEq` check on the length. -/
public theorem List.length_beq_eq {α : Type*} {l : List α} {n : ℕ}
    (h : l.length.beq n) : l.length = n := Nat.eq_of_beq_eq_true h

/-- Build the `hasRankGE_of_certificate` proof term directly. The `Certificate.Valid` checks are
packaged via its constructor: the five length checks and the five `Bool`
checks are discharged by `Lean.reflBoolTrue`, and the torsion check `|E(ℚ)[2]| ≤ 2^t` by
`certTorsionBound_zero` (two `Bool` witnesses) for `t = 0`, `certTorsionBound_one` (a short-model
root `R` plus three `Bool` witnesses) for `t = 1`, or the universal `certTorsionBound_two` for
`t = 2`. The model equality is discharged by `WeierstrassCurve.ext_of_beq` on the five coefficient
`BEq`s. `torsRoot` supplies the `t = 1` root `R`. -/
def mkCertProof (t : Nat) (torsRoot : Int) (wE a1E a2E a3E a4E a6E cExpr hW : Expr) :
    MetaM Expr := do
  let rb := Lean.reflBoolTrue
  let wModel := mkAppN (mkConst ``IntegralScaling.intShortModel) #[a1E, a2E, a3E, a4E, a6E]
  let (sA2E, sA4E, sA6E) := shortCoeffExprs a1E a2E a3E a4E a6E
  let wCurve := mkAppN (mkConst ``curve) #[sA2E, sA4E, sA6E]
  let hmodel := mkAppN (mkConst ``WeierstrassCurve.ext_of_beq)
    #[wModel, wCurve, rb, rb, rb, rb, rb]
  let ρE := mkApp (mkConst ``Certificate.ρ) cExpr
  let natTy := mkConst ``Nat
  let hlenOf (field : Name) (elemTy : Expr) : Expr :=
    mkAppN (mkConst ``List.length_beq_eq [Level.zero])
      #[elemTy, mkApp (mkConst field) cExpr, ρE, rb]
  let hlenP := hlenOf ``Certificate.points ratPairTy
  let hlenL := hlenOf ``Certificate.labels (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    natTy (mkConst ``Int))
  let hlenB := hlenOf ``Certificate.B natTy
  let hlenM := hlenOf ``Certificate.M natTy
  let hlenQ := hlenOf ``Certificate.qrMasks natTy
  -- The `2`-torsion bound, keyed to the certificate's coefficients so it matches `curve c.a₂ …`.
  let a2C := mkApp (mkConst ``Certificate.a₂) cExpr
  let a4C := mkApp (mkConst ``Certificate.a₄) cExpr
  let a6C := mkApp (mkConst ``Certificate.a₆) cExpr
  let tpC := mkApp (mkConst ``Certificate.torsionPrime) cExpr
  let htors :=
    if t == 0 then
      mkAppN (mkConst ``certTorsionBound_zero) #[a2C, a4C, a6C, tpC, rb, rb]
    else if t == 1 then
      mkAppN (mkConst ``certTorsionBound_one) #[a2C, a4C, a6C, tpC, toExpr torsRoot, rb, rb, rb]
    else
      mkAppN (mkConst ``certTorsionBound_two) #[a2C, a4C, a6C]
  let hValid := mkAppN (mkConst ``Certificate.Valid.mk)
    #[cExpr, hlenP, hlenL, hlenB, hlenM, hlenQ, rb, rb, rb, rb, rb, htors]
  return mkAppN (mkConst ``hasRankGE_of_certificate)
    #[a1E, a2E, a3E, a4E, a6E, cExpr, wE, hW, hmodel, hValid]

/-- Reads the goal curve `W`, its integer coefficients `a₁…a₆`, and target rank `ρ_goal`, parses
the two data files (`ρ_goal + t` entries each), computes the descent matrix and its `𝔽₂` inverse,
and assigns the `hasRankGE_of_certificate` proof term. `W = ⟨↑a₁, …, ↑a₆⟩` is proved by
`ext_of_beq` on five `reflBoolTrue` `BEq` checks, with no side goals. The certificate's `ρ` is
`ρ_goal + t`, so `rank ≥ ρ - t` is defeq to the goal `rank ≥ ρ_goal`. -/
def runCertify (t tpNat : Nat) (torsRoot : Int) (path lpath : String) : TacticM Unit := do
  let goal ← getMainGoal
  let (ρGoal, wE, v1, v2, v3, v4, v6) ← readGoal goal
  let a1E := toExpr v1
  let a2E := toExpr v2
  let a3E := toExpr v3
  let a4E := toExpr v4
  let a6E := toExpr v6
  let ρ := ρGoal + t
  let (pts, ls) ← readData path lpath ρ
  let xs := (pts.map fun (xn, xd, _, _) ↦ (xn, xd)).toList
  let (B, M) ← buildMats (v1 ^ 2 + 4 * v2) (16 * v4 + 8 * v1 * v3) xs ls.toList ρ
  let cExpr ← mkCertExpr ρ pts ls B M t tpNat a1E a2E a3E a4E a6E
  -- `W = ⟨↑a₁, …, ↑a₆⟩` via `ext_of_beq` on five ℚ-`BEq` checks, each `reflBoolTrue`.
  let ratTy := mkConst ``Rat
  let castE (aE : Expr) : Expr :=
    mkApp3 (mkConst ``Int.cast [Level.zero]) ratTy (mkConst ``Rat.instIntCast) aE
  let litCurve := mkAppN (mkConst ``WeierstrassCurve.mk [Level.zero])
    #[ratTy, castE a1E, castE a2E, castE a3E, castE a4E, castE a6E]
  let rb := Lean.reflBoolTrue
  let hW := mkAppN (mkConst ``WeierstrassCurve.ext_of_beq) #[wE, litCurve, rb, rb, rb, rb, rb]
  goal.assign (← mkCertProof t torsRoot wE a1E a2E a3E a4E a6E cExpr hW)
  replaceMainGoal []

elab_rules : tactic
  | `(tactic| certify_curve torsion $tp:num $path:str $lpath:str) => do
    runCertify 0 tp.getNat 0 path.getString lpath.getString
  | `(tactic| certify_curve fullTorsion $path:str $lpath:str) => do
    runCertify 2 0 0 path.getString lpath.getString
  | `(tactic| certify_curve oneTorsion $r:intLit $l:num $path:str $lpath:str) => do
    runCertify 1 l.getNat (← getIntLit r) path.getString lpath.getString

end ECCompute
