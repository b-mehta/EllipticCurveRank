/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.MainTheorem
import ECCompute.Certify.CertifyEval

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE W ρ`, where `W` is a Weierstrass curve over `ℚ` whose
coefficients are integers.  It reads the coefficients and rank from the goal (so the curve must be
`unfold`ed to a `WeierstrassCurve` literal first) and the generating points and descent labels from
two data files, computes the descent-character matrix and its `𝔽₂` inverse, and discharges the
referee obligations of `hasRankGE_of_certificate`.

Each data file has one entry per line.  A points file has `x y`, with each coordinate either an
integer or a reduced fraction `a/b`; a labels file has `p θ`, the descent character at the root `θ`
of the 2-division cubic mod `p`.

```
theorem hasRankGE_example : HasRankGE curveExample 29 := by
  unfold curveExample exampleA₄ exampleA₆   -- expose the `WeierstrassCurve` literal in the goal
  certify_curve torsion 67 points "data/example.txt" labels "data/example-labels.txt"
```
-/

open Lean Elab Tactic Meta

namespace ECCompute

/-- Extract the `Nat` value of a numeral `Expr` (trying the raw expression first, for `0`/`1` and
`OfNat` numerals, then its `whnf`, which unfolds abbreviations and projections). -/
private def getNatE (e : Expr) : MetaM Nat := do
  if let some n := (← whnfR e).nat? then return n     -- reducible: coeff abbrevs, `0`/`1`
  let e ← whnf e                                        -- full: unfold the point/label `def`s
  if let some n := e.nat? then return n
  if let some n ← getNatValue? e then return n          -- `OfNat` numerals behind a projection
  throwError "certify_curve: expected a `Nat` literal, got{indentExpr e}"

/-- Extract the `Int` value of a numeral `Expr`; see `getNatE`. -/
private def getIntE (e : Expr) : MetaM Int := do
  if let some n := (← whnfR e).int? then return n
  let e ← whnf e
  if let some n := e.int? then return n
  if let some n ← getIntValue? e then return n
  throwError "certify_curve: expected a `Int` literal, got{indentExpr e}"

/-- ASCII-trim, returning a `String`.  `String.trim` is deprecated in favour of `String.trimAscii`,
which returns a `String.Slice`, so we convert back. -/
private def strTrim (s : String) : String := s.trimAscii.toString

/-- Parse a coordinate string `"a"` or `"a/b"` into a *reduced* `(numerator, denominator)`. -/
private def parseCoord (s : String) : Int × Nat :=
  match (strTrim s).splitOn "/" with
  | [a, b] =>
    let num := (strTrim a).toInt!
    let den := (strTrim b).toNat!
    let g := Nat.gcd num.natAbs den
    if g == 0 then (num, den) else (num / (g : Int), den / g)
  | _ => ((strTrim s).toInt!, 1)

/-- Parse one line `"x y"` of a points file into `(x.num, x.den, y.num, y.den)`. -/
private def parseLine (line : String) : Int × Nat × Int × Nat :=
  match ((strTrim line).splitOn " ").filter (· ≠ "") with
  | [xs, ys] => let (xn, xd) := parseCoord xs; let (yn, yd) := parseCoord ys; (xn, xd, yn, yd)
  | _ => (0, 1, 0, 1)

/-- `ℚ` Expr for `num / den` (reduced) via the proof-free `mkRat`; normalization is kernel
computation, so no `Coprime`/`den ≠ 0` proof is constructed. -/
private def coordExpr (num : Int) (den : Nat) : Expr :=
  mkApp2 (mkConst ``mkRat) (toExpr num) (toExpr den)

/-- Parse one line `"p θ"` of a labels file into the descent column `(p, θ)`. -/
private def parseLabel (line : String) : Nat × Int :=
  match ((strTrim line).splitOn " ").filter (· ≠ "") with
  | [p, t] => ((strTrim p).toNat!, (strTrim t).toInt!)
  | _ => (0, 0)

/-- Syntax of the `certify_curve` tactic; see the module docstring.  The `torsion ℓ` form concedes
`t = 0` with witness prime `ℓ` (trivial rational `2`-torsion); the `oneTorsion root R witness ℓ`
form concedes `t = 1` by naming the short-model root `R` of the `2`-division cubic and a prime `ℓ`
at which the quadratic cofactor has no root; the `fullTorsion` form concedes `t = 2` (full rational
`2`-torsion, e.g. square-discriminant curves) via the universal bound. -/
syntax (name := certifyCurve) "certify_curve" " torsion " term:max " points " str
  " labels " str : tactic

syntax (name := certifyCurveFull) "certify_curve" " fullTorsion " " points " str
  " labels " str : tactic

syntax (name := certifyCurveOne) "certify_curve" " oneTorsion " " root " term:max
  " witness " term:max " points " str " labels " str : tactic

/-- Extract the integer value of an integer-valued `ℚ` literal `Expr`: an `OfNat` numeral, its
negation, or an `Int.cast` of an `ℤ` literal.  Errors if the coefficient is not an integer. -/
private def getRatIntE (e : Expr) : MetaM Int := do
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
integer-valued rational coefficients.  Returns the rank `ρ`, the original curve `Expr` `W`, and the
five integer coefficient values. -/
private def readGoal (goal : MVarId) :
    MetaM (Nat × Expr × Int × Int × Int × Int × Int) := do
  let (``HasRankGE, #[curveE, rhoE]) := (← goal.getType).getAppFnArgs
    | throwError "certify_curve: goal must be `HasRankGE _ _`"
  let (``WeierstrassCurve.mk, #[_, q1E, q2E, q3E, q4E, q6E]) := (← whnf curveE).getAppFnArgs
    | throwError "certify_curve: the curve must reduce to a `WeierstrassCurve` literal; \
        `unfold` your curve definition and its coefficient abbreviations first"
  return (← getNatE rhoE, curveE,
    ← getRatIntE q1E, ← getRatIntE q2E, ← getRatIntE q3E, ← getRatIntE q4E, ← getRatIntE q6E)

/-- Read and parse the points file (`x y` per line) and labels file (`p θ`), checking each has
`rho` entries. -/
private def readData (path lpath : String) (rho : Nat) :
    MetaM (Array (Int × Nat × Int × Nat) × Array (Nat × Int)) := do
  let pts := ((← IO.FS.readFile path).splitOn "\n").filterMap fun l =>
    if (strTrim l).isEmpty then none else some (parseLine l)
  let lbls := ((← IO.FS.readFile lpath).splitOn "\n").filterMap fun l =>
    if (strTrim l).isEmpty then none else some (parseLabel l)
  if pts.length ≠ rho then
    throwError "certify_curve: points file has {pts.length} points but the goal rank is {rho}"
  if lbls.length ≠ rho then
    throwError "certify_curve: labels file has {lbls.length} labels but the goal rank is {rho}"
  return (pts.toArray, lbls.toArray)

/-- The descent-character matrix over the short model and its 𝔽₂ inverse (a pure computation). -/
private def buildMats (sA2 sA4 : Int) (xs : List (Int × Nat)) (ls : List (Nat × Int)) (rho : Nat) :
    MetaM (List Nat × List Nat) := do
  let matB := CertifyEval.computeMatB sA2 sA4 xs ls
  let some matM := CertifyEval.invF2 matB.toArray rho
    | throwError "certify_curve: the descent-character matrix is singular over 𝔽₂"
  return (matB, matM)

/-- Build the `Certificate` Expr directly with the `Meta` API (no `Syntax`/`quote`/`delab`). -/
private def mkCertExpr (rho : Nat) (pts : Array (Int × Nat × Int × Nat)) (ls : Array (Nat × Int))
    (matB matM : List Nat) (t tp : Nat) (a1E a2E a3E a4E a6E : Expr) : MetaM Expr := do
  let ratTy := mkConst ``Rat
  let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) ratTy ratTy
  let ptExprs := pts.toList.map fun (xn, xd, yn, yd) =>
    mkAppN (mkConst ``Prod.mk [Level.zero, Level.zero])
      #[ratTy, ratTy, coordExpr xn xd, coordExpr yn yd]
  let pointsE ← mkListLit pairTy ptExprs
  return mkAppN (mkConst ``Certificate.mk)
    #[toExpr (0 : Int), mkApp2 (mkConst ``ModelChange.intShortA₂) a1E a2E, toExpr (0 : Int),
      mkApp3 (mkConst ``ModelChange.intShortA₄) a1E a3E a4E,
      mkApp2 (mkConst ``ModelChange.intShortA₆) a3E a6E, toExpr rho, pointsE,
      toExpr ls.toList, toExpr matB, toExpr matM, toExpr t, toExpr tp]

/-- Build the `hasRankGE_of_certificate` proof term directly.  The model equality (via
`WeierstrassCurve.ext_of_beq` on the five coefficient `BEq`s), the four length obligations, and the
five referee `Bool` checks are all discharged by `Lean.reflBoolTrue`.  The torsion obligation
`|E(ℚ)[2]| ≤ 2^t` is discharged by `certTorsionBound_zero` (two `Bool` witnesses) for `t = 0`,
`certTorsionBound_one` (a short-model root `R` plus three `Bool` witnesses) for `t = 1`, or the
universal `certTorsionBound_two` for `t = 2`.  `torsRoot` supplies the `t = 1` root `R`. -/
private def mkCertProof (t : Nat) (torsRoot : Int) (wE a1E a2E a3E a4E a6E cExpr hW : Expr) :
    MetaM Expr := do
  let rb := Lean.reflBoolTrue
  let wModel := mkAppN (mkConst ``ModelChange.intShortModel) #[a1E, a2E, a3E, a4E, a6E]
  let wCurve := mkAppN (mkConst ``curve)
    #[mkApp2 (mkConst ``ModelChange.intShortA₂) a1E a2E,
      mkApp3 (mkConst ``ModelChange.intShortA₄) a1E a3E a4E,
      mkApp2 (mkConst ``ModelChange.intShortA₆) a3E a6E]
  let hmodel := mkAppN (mkConst ``WeierstrassCurve.ext_of_beq)
    #[wModel, wCurve, rb, rb, rb, rb, rb]
  let rhoE := mkApp (mkConst ``Certificate.rho) cExpr
  let natTy := mkConst ``Nat
  let hlenOf (field : Name) (elemTy : Expr) : Expr :=
    let lenE := mkAppN (mkConst ``List.length [Level.zero]) #[elemTy, mkApp (mkConst field) cExpr]
    mkAppN (mkConst ``Nat.eq_of_beq_eq_true) #[lenE, rhoE, rb]
  let hlenP := hlenOf ``Certificate.points (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat))
  let hlenL := hlenOf ``Certificate.labels (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    natTy (mkConst ``Int))
  let hlenB := hlenOf ``Certificate.matB natTy
  let hlenM := hlenOf ``Certificate.matM natTy
  -- The `2`-torsion bound, keyed to the certificate's coefficients so it matches `curve c.a₂ …`.
  let a2C := mkApp (mkConst ``Certificate.a₂) cExpr
  let a4C := mkApp (mkConst ``Certificate.a₄) cExpr
  let a6C := mkApp (mkConst ``Certificate.a₆) cExpr
  let tpC := mkApp (mkConst ``Certificate.torsionPrime) cExpr
  let htors :=
    if t == 0 then
      mkAppN (mkConst ``certTorsionBound_zero) #[a2C, a4C, a6C, tpC, rb, rb]
    else if t == 1 then
      mkAppN (mkConst ``certTorsionBound_one) #[a2C, a4C, a6C, toExpr torsRoot, tpC, rb, rb, rb]
    else
      mkAppN (mkConst ``certTorsionBound_two) #[a2C, a4C, a6C]
  return mkAppN (mkConst ``hasRankGE_of_certificate)
    #[a1E, a2E, a3E, a4E, a6E, cExpr, wE, hW,
      hmodel, hlenP, hlenL, hlenB, hlenM, rb, rb, rb, rb, rb, htors]

/-- The shared driver: read the goal curve `W`, its integer coefficients `a₁…a₆`, and target rank
`ρ_goal`, parse the two data files (which must have `ρ_goal + t` entries), compute the descent
matrix and its `𝔽₂` inverse, and assign the `hasRankGE_of_certificate` proof term.  The coefficient
bridge `W = ⟨↑a₁, …, ↑a₆⟩` is built purely with `ext_of_beq` on five `reflBoolTrue` `BEq` checks (no
side goals).  The certificate's `rho` is `ρ_goal + t`, so its conclusion `rank ≥ rho - t` is defeq to
the goal `rank ≥ ρ_goal`. -/
private def runCertify (t tpNat : Nat) (torsRoot : Int) (path lpath : String) : TacticM Unit := do
  let goal ← getMainGoal
  let (rhoGoal, wE, v1, v2, v3, v4, v6) ← readGoal goal
  let a1E := toExpr v1
  let a2E := toExpr v2
  let a3E := toExpr v3
  let a4E := toExpr v4
  let a6E := toExpr v6
  let rho := rhoGoal + t
  let (pts, lbls) ← readData path lpath rho
  let xs := (pts.map fun (xn, xd, _, _) => (xn, xd)).toList
  let (matB, matM) ← buildMats (v1 ^ 2 + 4 * v2) (16 * v4 + 8 * v1 * v3) xs lbls.toList rho
  let cExpr ← mkCertExpr rho pts lbls matB matM t tpNat a1E a2E a3E a4E a6E
  -- The coefficient bridge `W = ⟨↑a₁, …, ↑a₆⟩` via `ext_of_beq` on five ℚ-`BEq` checks, each a
  -- kernel-reducible `reflBoolTrue`: pure `Expr`, no side goals.
  let ratTy := mkConst ``Rat
  let castE (aE : Expr) : Expr :=
    mkApp3 (mkConst ``Int.cast [Level.zero]) ratTy (mkConst ``Rat.instIntCast) aE
  let litCurve := mkAppN (mkConst ``WeierstrassCurve.mk [Level.zero])
    #[ratTy, castE a1E, castE a2E, castE a3E, castE a4E, castE a6E]
  let rb := Lean.reflBoolTrue
  let hW := mkAppN (mkConst ``WeierstrassCurve.ext_of_beq) #[wE, litCurve, rb, rb, rb, rb, rb]
  goal.assign (← mkCertProof t torsRoot wE a1E a2E a3E a4E a6E cExpr hW)
  replaceMainGoal []

@[tactic certifyCurve]
def evalCertifyCurve : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve torsion $tp points $path:str labels $lpath:str) => do
    let tpNat ← getNatE (← elabTermEnsuringType tp (mkConst ``Nat))
    runCertify 0 tpNat 0 path.getString lpath.getString
  | _ => throwUnsupportedSyntax

@[tactic certifyCurveFull]
def evalCertifyCurveFull : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve fullTorsion points $path:str labels $lpath:str) => do
    runCertify 2 0 0 path.getString lpath.getString
  | _ => throwUnsupportedSyntax

@[tactic certifyCurveOne]
def evalCertifyCurveOne : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve oneTorsion root $r witness $l points $path:str labels $lpath:str) => do
    let torsRoot ← getIntE (← elabTermEnsuringType r (mkConst ``Int))
    let tpNat ← getNatE (← elabTermEnsuringType l (mkConst ``Nat))
    runCertify 1 tpNat torsRoot path.getString lpath.getString
  | _ => throwUnsupportedSyntax

end ECCompute
