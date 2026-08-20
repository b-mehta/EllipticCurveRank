/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.MainTheorem
import ECCompute.Tactic.CertifyEval

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE W ρ`, where `W` is a Weierstrass curve over `ℚ` whose
coefficients are integers. It reads the coefficients and rank from the goal (so the curve must be
`unfold`ed to a `WeierstrassCurve` literal first) and the generating points and descent labels from
two data files, computes the descent-character matrix and its `𝔽₂` inverse, and discharges the
referee obligations of `hasRankGE_of_certificate`.

Each data file has one entry per line. A points file has `x y`, with each coordinate either an
integer or a reduced fraction `a/b`; a labels file has `p θ`, the descent character at the root `θ`
of the 2-division cubic mod `p`.

```
theorem hasRankGE_example : HasRankGE curveExample 29 := by
  unfold curveExample   -- expose the `WeierstrassCurve` literal in the goal
  certify_curve torsion 67 points "data/example.txt" labels "data/example-labels.txt"
```
-/

open Lean Elab Tactic Meta

namespace ECCompute

/-- Extract a literal from `e` by trying `parse` on the raw expression, then on its `whnf`, then
the `fallback` extractor. `kind` names the expected type in the error message. -/
private def getLitE {α} (kind : String) (parse : Expr → Option α)
    (fallback : Expr → MetaM (Option α)) (e : Expr) : MetaM α := do
  if let some n := parse (← whnfR e) then return n
  let e ← whnf e
  if let some n := parse e then return n
  if let some n ← fallback e then return n
  throwError "certify_curve: expected a `{kind}` literal, got{indentExpr e}"

/-- Extract the `Nat` value of a numeral `Expr`. -/
private def getNatE (e : Expr) : MetaM Nat := getLitE "Nat" (·.nat?) getNatValue? e

/-- Extract the `Int` value of a numeral `Expr`; see `getNatE`. -/
private def getIntE (e : Expr) : MetaM Int := getLitE "Int" (·.int?) getIntValue? e

/-- ASCII-trim `s`, returning a `String`. -/
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
private def parseLine (line : String) : Option (Int × Nat × Int × Nat) :=
  match ((strTrim line).splitOn " ").filter (· ≠ "") with
  | [xs, ys] => let (xn, xd) := parseCoord xs; let (yn, yd) := parseCoord ys; some (xn, xd, yn, yd)
  | _ => none

/-- The `ℚ` literal `num / den` as an `Expr`, built with `mkRat`, which leaves the reduction to
kernel computation. -/
private def coordExpr (num : Int) (den : Nat) : Expr :=
  mkApp2 (mkConst ``mkRat) (toExpr num) (toExpr den)

/-- Parse one line `"p θ"` of a labels file into the descent column `(p, θ)`. -/
private def parseLabel (line : String) : Option (Nat × Int) :=
  match ((strTrim line).splitOn " ").filter (· ≠ "") with
  | [p, t] => some ((strTrim p).toNat!, (strTrim t).toInt!)
  | _ => none

/-- `certify_curve torsion ℓ` concedes `t = 0`, trivial rational `2`-torsion, with `ℓ` a prime at
which the `2`-division cubic has no root. -/
syntax "certify_curve" " torsion " term:max " points " str " labels " str : tactic

/-- `certify_curve fullTorsion` concedes `t = 2`, full rational `2`-torsion, via the bound
`|E(ℚ)[2]| ≤ 4` that holds for every curve. -/
syntax "certify_curve" " fullTorsion " " points " str " labels " str : tactic

/-- `certify_curve oneTorsion root R witness ℓ` concedes `t = 1`, naming the short-model root `R`
of the `2`-division cubic and a prime `ℓ` at which the quadratic cofactor has no root. -/
syntax "certify_curve" " oneTorsion " " root " term:max " witness " term:max
  " points " str " labels " str : tactic

/-- Extract the integer value of an integer-valued `ℚ` literal `Expr`: an `OfNat` numeral, its
negation, or an `Int.cast` of an `ℤ` literal. Errors if the coefficient is not an integer. -/
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
integer-valued rational coefficients. Returns the rank `ρ`, the original curve `Expr` `W`, and the
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
`rhoGoal + torsionDim` entries, the certificate's `rho`. -/
private def readData (pointsPath labelsPath : String) (rhoGoal torsionDim : Nat) :
    MetaM (Array (Int × Nat × Int × Nat) × Array (Nat × Int)) := do
  let rho := rhoGoal + torsionDim
  let pts ← (((← IO.FS.readFile pointsPath).splitOn "\n").filter fun l =>
      !(strTrim l).isEmpty).mapM
    fun l => match parseLine l with
      | some p => pure p
      | none => throwError "certify_curve: malformed points line: {l}"
  let lbls ← (((← IO.FS.readFile labelsPath).splitOn "\n").filter fun l =>
      !(strTrim l).isEmpty).mapM
    fun l => match parseLabel l with
      | some x => pure x
      | none => throwError "certify_curve: malformed labels line: {l}"
  if pts.length ≠ rho then
    throwError "certify_curve: points file has {pts.length} points but the certificate needs \
      {rho} = {rhoGoal} + {torsionDim}"
  if lbls.length ≠ rho then
    throwError "certify_curve: labels file has {lbls.length} labels but the certificate needs \
      {rho} = {rhoGoal} + {torsionDim}"
  return (pts.toArray, lbls.toArray)

/-- The descent-character matrix over the short model `y² = x³ + shortA₂x² + shortA₄x + a₆` and
its 𝔽₂ inverse (a pure computation). -/
private def buildMats (shortA₂ shortA₄ : Int) (xs : List (Int × Nat)) (ls : List (Nat × Int))
    (rho : Nat) : MetaM (List Nat × List Nat) := do
  let matB := CertifyEval.computeMatB shortA₂ shortA₄ xs ls
  let some matM := CertifyEval.invF2 matB.toArray rho
    | throwError "certify_curve: the descent-character matrix is singular over 𝔽₂"
  return (matB, matM)

/-- The pair type `ℚ × ℚ` as an `Expr`. -/
private def ratPairTy : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Rat) (mkConst ``Rat)

/-- The short-model coefficient Exprs `(a₂, a₄, a₆)` built from the integer coefficient Exprs
`a₁…a₆` via `IntegralScaling.intShortA₂/₄/₆`. -/
private def shortCoeffExprs (a1E a2E a3E a4E a6E : Expr) : Expr × Expr × Expr :=
  (mkApp2 (mkConst ``IntegralScaling.intShortA₂) a1E a2E,
    mkApp3 (mkConst ``IntegralScaling.intShortA₄) a1E a3E a4E,
    mkApp2 (mkConst ``IntegralScaling.intShortA₆) a3E a6E)

/-- Build the `Certificate` `Expr` whose short-model coefficients come from the general-model
coefficient Exprs `a1E … a6E`, with `torsionDim` the certified `2`-torsion exponent and
`torsionPrime` its witness prime. -/
private def mkCertExpr (rho : Nat) (pts : Array (Int × Nat × Int × Nat)) (ls : Array (Nat × Int))
    (matB matM : List Nat) (torsionDim torsionPrime : Nat) (a1E a2E a3E a4E a6E : Expr) :
    MetaM Expr := do
  let ratTy := mkConst ``Rat
  let pairTy := ratPairTy
  let ptExprs := pts.toList.map fun (xn, xd, yn, yd) =>
    mkAppN (mkConst ``Prod.mk [Level.zero, Level.zero])
      #[ratTy, ratTy, coordExpr xn xd, coordExpr yn yd]
  let pointsE ← mkListLit pairTy ptExprs
  let (sA2E, sA4E, sA6E) := shortCoeffExprs a1E a2E a3E a4E a6E
  let qms := ls.toList.map fun l => CertifyEval.qrMaskNat l.1
  return mkAppN (mkConst ``Certificate.mk)
    #[sA2E, sA4E, sA6E, toExpr rho, pointsE,
      toExpr ls.toList, toExpr matB, toExpr matM, toExpr qms, toExpr torsionDim,
      toExpr torsionPrime]

/-- The equality `lhs = rhs` of two Weierstrass curves over `ℚ`, proved by
`WeierstrassCurve.ext_of_beq` on five kernel-reducible coefficient `BEq` checks. -/
private def mkExtOfBeq (lhs rhs : Expr) : Expr :=
  let rb := reflBoolTrue
  mkAppN (mkConst ``WeierstrassCurve.ext_of_beq) #[lhs, rhs, rb, rb, rb, rb, rb]

/-- Build the `hasRankGE_of_certificate` application for the certificate `cExpr`. The torsion
obligation is discharged by `certTorsionBound_zero`, `certTorsionBound_one` or
`certTorsionBound_two` according to `torsionDim`, with `torsionRoot` supplying the short-model
root the `torsionDim = 1` bound needs. -/
private def mkCertProof (torsionDim : Nat) (torsionRoot : Int)
    (wE a1E a2E a3E a4E a6E cExpr hW : Expr) : MetaM Expr := do
  let rb := reflBoolTrue
  let wModel := mkAppN (mkConst ``IntegralScaling.intShortModel) #[a1E, a2E, a3E, a4E, a6E]
  let (sA2E, sA4E, sA6E) := shortCoeffExprs a1E a2E a3E a4E a6E
  let hmodel := mkExtOfBeq wModel (mkAppN (mkConst ``curve) #[sA2E, sA4E, sA6E])
  let rhoE := mkApp (mkConst ``Certificate.rho) cExpr
  let natTy := mkConst ``Nat
  let hlenOf (field : Name) (elemTy : Expr) : Expr :=
    mkAppN (mkConst ``length_eq_of_beq [Level.zero])
      #[elemTy, mkApp (mkConst field) cExpr, rhoE, rb]
  let hlenP := hlenOf ``Certificate.points ratPairTy
  let hlenL := hlenOf ``Certificate.labels (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    natTy (mkConst ``Int))
  let hlenB := hlenOf ``Certificate.matB natTy
  let hlenM := hlenOf ``Certificate.matM natTy
  let hlenQ := hlenOf ``Certificate.qrMasks natTy
  -- The `2`-torsion bound, keyed to the certificate's coefficients so it matches `curve c.a₂ …`.
  let a2C := mkApp (mkConst ``Certificate.a₂) cExpr
  let a4C := mkApp (mkConst ``Certificate.a₄) cExpr
  let a6C := mkApp (mkConst ``Certificate.a₆) cExpr
  let tpC := mkApp (mkConst ``Certificate.torsionPrime) cExpr
  let htors :=
    if torsionDim == 0 then
      mkAppN (mkConst ``certTorsionBound_zero) #[a2C, a4C, a6C, tpC, rb, rb]
    else if torsionDim == 1 then
      mkAppN (mkConst ``certTorsionBound_one)
        #[a2C, a4C, a6C, toExpr torsionRoot, tpC, rb, rb, rb]
    else
      mkAppN (mkConst ``certTorsionBound_two) #[a2C, a4C, a6C]
  return mkAppN (mkConst ``hasRankGE_of_certificate)
    #[a1E, a2E, a3E, a4E, a6E, cExpr, wE, hW,
      hmodel, hlenP, hlenL, hlenB, hlenM, hlenQ, rb, rb, rb, rb, rb, htors]

/-- Read the goal curve `W`, its integer coefficients `a₁…a₆` and target rank `ρ_goal`, parse the
two data files, compute the descent matrix and its `𝔽₂` inverse, and assign the
`hasRankGE_of_certificate` proof term. The certificate's `rho` is `ρ_goal + torsionDim`, so
`rank ≥ rho - torsionDim` is defeq to the goal `rank ≥ ρ_goal`. -/
private def runCertify (torsionDim torsionPrime : Nat) (torsionRoot : Int)
    (pointsPath labelsPath : String) : TacticM Unit := do
  let goal ← getMainGoal
  let (rhoGoal, wE, v1, v2, v3, v4, v6) ← readGoal goal
  let a1E := toExpr v1
  let a2E := toExpr v2
  let a3E := toExpr v3
  let a4E := toExpr v4
  let a6E := toExpr v6
  let rho := rhoGoal + torsionDim
  let (pts, lbls) ← readData pointsPath labelsPath rhoGoal torsionDim
  let xs := (pts.map fun (xn, xd, _, _) => (xn, xd)).toList
  let (matB, matM) ← buildMats (v1 ^ 2 + 4 * v2) (16 * v4 + 8 * v1 * v3) xs lbls.toList rho
  let cExpr ← mkCertExpr rho pts lbls matB matM torsionDim torsionPrime a1E a2E a3E a4E a6E
  let ratTy := mkConst ``Rat
  let castE (aE : Expr) : Expr :=
    mkApp3 (mkConst ``Int.cast [Level.zero]) ratTy (mkConst ``Rat.instIntCast) aE
  let litCurve := mkAppN (mkConst ``WeierstrassCurve.mk [Level.zero])
    #[ratTy, castE a1E, castE a2E, castE a3E, castE a4E, castE a6E]
  goal.assign (← mkCertProof torsionDim torsionRoot wE a1E a2E a3E a4E a6E cExpr
    (mkExtOfBeq wE litCurve))
  replaceMainGoal []

elab_rules : tactic
  | `(tactic| certify_curve torsion $tp points $pointsPath:str labels $labelsPath:str) => do
    let torsionPrime ← getNatE (← elabTermEnsuringType tp (mkConst ``Nat))
    runCertify 0 torsionPrime 0 pointsPath.getString labelsPath.getString
  | `(tactic| certify_curve fullTorsion points $pointsPath:str labels $labelsPath:str) =>
    runCertify 2 0 0 pointsPath.getString labelsPath.getString
  | `(tactic| certify_curve oneTorsion root $r witness $l points $pointsPath:str
      labels $labelsPath:str) => do
    let torsionRoot ← getIntE (← elabTermEnsuringType r (mkConst ``Int))
    let torsionPrime ← getNatE (← elabTermEnsuringType l (mkConst ``Nat))
    runCertify 1 torsionPrime torsionRoot pointsPath.getString labelsPath.getString

end ECCompute
