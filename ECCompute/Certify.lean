/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.MainTheorem
import ECCompute.Certify.CertifyEval

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) ρ`.  It reads the coefficients
and rank from the goal (so the curve must be `unfold`ed to literals first) and the generating points
and descent labels from two data files, computes the descent-character matrix and its `𝔽₂` inverse,
and discharges the referee obligations of `hasRankGE_of_certificate`.

Each data file has one entry per line.  A points file has `x y`, with each coordinate either an
integer or a reduced fraction `a/b`; a labels file has `p θ`, the descent character at the root `θ`
of the 2-division cubic mod `p`.

```
theorem hasRankGE_example : HasRankGE curveExample 29 := by
  unfold curveExample exampleA₄ exampleA₆   -- expose `toCurveQ 1 0 0 <lit> <lit>` in the goal
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

/-- Syntax of the `certify_curve` tactic; see the module docstring. -/
syntax (name := certifyCurve) "certify_curve" " torsion " term:max " points " str
  " labels " str : tactic

/-- Read `HasRankGE (toCurveQ a₁…a₆) ρ` off `goal`: rank `ρ` and the five coefficient `Expr`s. -/
private def readGoal (goal : MVarId) : MetaM (Nat × Expr × Expr × Expr × Expr × Expr) := do
  let (``HasRankGE, #[curveE, rhoE]) := (← goal.getType).getAppFnArgs
    | throwError "certify_curve: goal must be `HasRankGE _ _`"
  let (``ModelIso.toCurveQ, #[a1E, a2E, a3E, a4E, a6E]) := curveE.getAppFnArgs
    | throwError "certify_curve: the curve must be `toCurveQ …`; `unfold` your curve definition \
        and its coefficient abbreviations first"
  return (← getNatE rhoE, a1E, a2E, a3E, a4E, a6E)

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
    (matB matM : List Nat) (tp : Nat) (a1E a2E a3E a4E a6E : Expr) : MetaM Expr := do
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
      toExpr ls.toList, toExpr matB, toExpr matM, toExpr (0 : Nat), toExpr tp]

/-- Build the `hasRankGE_of_certificate` proof term directly.  Every referee obligation is a
kernel-reducible `Bool` check discharged by `Lean.reflBoolTrue`: the model equality via
`WeierstrassCurve.ext_of_beq` on the five coefficient `BEq`s, and the four length obligations plus
`t = 0` via `Nat.eq_of_beq_eq_true`. -/
private def mkCertProof (rho : Nat) (a1E a2E a3E a4E a6E cExpr : Expr) : MetaM Expr := do
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
  let ht := mkAppN (mkConst ``Nat.eq_of_beq_eq_true)
    #[mkApp (mkConst ``Certificate.t) cExpr, toExpr (0 : Nat), rb]
  return mkAppN (mkConst ``hasRankGE_of_certificate)
    #[a1E, a2E, a3E, a4E, a6E, cExpr,
      hmodel, hlenP, hlenL, hlenB, hlenM, rb, rb, rb, rb, rb, ht, rb, rb]

@[tactic certifyCurve]
def evalCertifyCurve : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve torsion $tp points $path:str labels $lpath:str) => do
    -- read the coefficients `a₁…a₆` and rank `ρ` from the goal (so the curve and its coefficient
    -- abbreviations must already be `unfold`ed to literals), then parse the two data files
    let goal ← getMainGoal
    let (rho, a1E, a2E, a3E, a4E, a6E) ← readGoal goal
    let v1 ← getIntE a1E
    let v2 ← getIntE a2E
    let v3 ← getIntE a3E
    let v4 ← getIntE a4E
    let tpNat ← getNatE (← elabTermEnsuringType tp (mkConst ``Nat))
    let (pts, lbls) ← readData path.getString lpath.getString rho
    let xs := (pts.map fun (xn, xd, _, _) => (xn, xd)).toList
    -- compute the character matrix and its 𝔽₂ inverse, then build the proof term directly
    let (matB, matM) ← buildMats (v1 ^ 2 + 4 * v2) (16 * v4 + 8 * v1 * v3) xs lbls.toList rho
    let cExpr ← mkCertExpr rho pts lbls matB matM tpNat a1E a2E a3E a4E a6E
    goal.assign (← mkCertProof rho a1E a2E a3E a4E a6E cExpr)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end ECCompute
