/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.MainTheorem
import ECCompute.CertifyEval

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) ρ`.  It reads the coefficients
`a₁…a₆` and the rank `ρ` out of the goal (so the curve and its coefficient abbreviations must be
`unfold`ed to literals first), takes a torsion witness prime, and reads the generating points and
descent labels from two data files.  From these it computes the descent-character matrix `matB` and
its `𝔽₂` inverse `matM` with the fast helpers in `ECCompute.CertifyEval`, assembles the
`Certificate`, and discharges the referee obligations of `hasRankGE_of_certificate` in one proof
term.

Each data file has one entry per line.  A points file has `x y`, with each coordinate either an
integer or a reduced fraction `a/b`; a labels file has `p θ`, the descent character at the root `θ`
of the 2-division cubic mod `p`.

Nothing in `CertifyEval` is trusted: the assembled certificate's obligations (`hB`, `hinv`, …) are
kernel-checked exactly as a hand-written certificate would be, so a wrong matrix only makes the
tactic *fail to close the goal*, never certify a false bound.

```
theorem hasRankGE_example : HasRankGE curveExample 29 := by
  unfold curveExample exampleA₄ exampleA₆   -- expose `toCurveQ 1 0 0 <lit> <lit>` in the goal
  certify_curve torsion 67 points "data/example.txt" labels "data/example-labels.txt"
```
-/

open Lean Elab Tactic Meta

namespace ECCompute

/-- Extract the `Nat` value of a numeral `Expr` (trying the raw expression first — for `0`/`1` and
`OfNat` numerals — then its `whnf`, which unfolds abbreviations and projections). -/
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

/-- Syntax term for an `Int` literal. -/
private def intStx (n : Int) : MetaM Term :=
  if n < 0 then `(-$(quote n.natAbs)) else `($(quote n.toNat))

/-- Syntax term for the rational `num / den` (assumed reduced), in a kernel-reducible form: an
integer literal when `den = 1`, otherwise the smart constructor `Rat.mk'`. -/
private def coordStx (num : Int) (den : Nat) : MetaM Term := do
  let n ← intStx num
  if den == 1 then `(($n : ℚ))
  else `(Rat.mk' $n $(quote den) (by norm_num) (by norm_num))

/-- Parse one line `"p θ"` of a labels file into the descent column `(p, θ)`. -/
private def parseLabel (line : String) : Nat × Int :=
  match ((strTrim line).splitOn " ").filter (· ≠ "") with
  | [p, t] => ((strTrim p).toNat!, (strTrim t).toInt!)
  | _ => (0, 0)

/-- Syntax term for a label `(p, θ) : ℕ × ℤ`. -/
private def labelStx (p : Nat) (θ : Int) : MetaM Term := do
  `(($(quote p), $(← intStx θ)))

/-- Syntax of the `certify_curve` tactic; see the module docstring. -/
syntax (name := certifyCurve) "certify_curve" " torsion " term:max " points " str
  " labels " str : tactic

@[tactic certifyCurve]
def evalCertifyCurve : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve torsion $tp points $path:str labels $lpath:str) => do
    -- read the coefficients `a₁…a₆` and the rank `ρ` out of the goal
    -- `HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) ρ` (so the curve and its coefficient abbreviations must
    -- already be `unfold`ed to literals)
    let goal ← getMainGoal
    let (``HasRankGE, #[curveE, rhoE]) := (← goal.getType).getAppFnArgs
      | throwError "certify_curve: goal must be `HasRankGE _ _`"
    let rho ← getNatE rhoE
    let (``ModelIso.toCurveQ, #[a1E, a2E, a3E, a4E, a6E]) := curveE.getAppFnArgs
      | throwError "certify_curve: the curve must be `toCurveQ …`; `unfold` your curve definition \
          and its coefficient abbreviations first"
    let v1 ← getIntE a1E; let v2 ← getIntE a2E; let v3 ← getIntE a3E; let v4 ← getIntE a4E
    let sA2 := v1 ^ 2 + 4 * v2
    let sA4 := 16 * v4 + 8 * v1 * v3
    -- read and parse the points file (one `x y` per line, coordinates as `a/b`)
    let pts := ((← IO.FS.readFile path.getString).splitOn "\n").filterMap fun l =>
      if (strTrim l).isEmpty then none else some (parseLine l)
    let lbls := ((← IO.FS.readFile lpath.getString).splitOn "\n").filterMap fun l =>
      if (strTrim l).isEmpty then none else some (parseLabel l)
    if pts.length ≠ rho then
      throwError "certify_curve: points file has {pts.length} points but the goal rank is {rho}"
    if lbls.length ≠ rho then
      throwError "certify_curve: labels file has {lbls.length} labels but the goal rank is {rho}"
    let xs := (pts.map fun (xn, xd, _, _) => (xn, xd)).toArray
    let ls := lbls.toArray
    -- the character matrix and its 𝔽₂ inverse (a pure, compiled computation)
    let matB := CertifyEval.computeMatB sA2 sA4 xs.toList ls.toList
    let some matM := CertifyEval.invF2 matB.toArray rho
      | throwError "certify_curve: the descent-character matrix is singular over 𝔽₂"
    -- generate the parsed points and labels as plain `List` literals, spliced into the proof term.
    -- Every referee obligation is a kernel-reducible `Bool` check over these lists (closed by
    -- `quickRfl`), so the kernel never applies a `Fin ρ → _` family.
    let ptStxs ← pts.toArray.mapM fun (xn, xd, yn, yd) => do
      let xc ← coordStx xn xd
      let yc ← coordStx yn yd
      `(($xc, $yc))
    let labStxs ← ls.mapM fun (p, θ) => labelStx p θ
    let rhoStx : Term := quote rho
    let matBStx : Term := quote matB
    let matMStx : Term := quote matM
    let a1S ← Lean.PrettyPrinter.delab a1E; let a2S ← Lean.PrettyPrinter.delab a2E
    let a3S ← Lean.PrettyPrinter.delab a3E; let a4S ← Lean.PrettyPrinter.delab a4E
    let a6S ← Lean.PrettyPrinter.delab a6E
    let term ← `(
        let c : Certificate :=
          { a₁ := 0, a₂ := ModelChange.intShortA₂ $a1S $a2S, a₃ := 0,
            a₄ := ModelChange.intShortA₄ $a1S $a3S $a4S, a₆ := ModelChange.intShortA₆ $a3S $a6S,
            rho := $rhoStx, «points» := [$ptStxs,*], «labels» := [$labStxs,*],
            matB := $matBStx, matM := $matMStx, t := 0, torsionPrime := $tp }
        hasRankGE_of_certificate $a1S $a2S $a3S $a4S $a6S c
          rfl rfl rfl rfl rfl
          (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
          rfl (by decide)
          (by rw [← Bool.not_eq_true', ← Bool.not'_eq_not]; quickRfl))
    let e ← elabTermEnsuringType term (← goal.getType)
    Term.synthesizeSyntheticMVarsNoPostponing
    goal.assign (← instantiateMVars e)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end ECCompute
