/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.CurveCertificate
import ECCompute.CertifyEval
import Qq

/-!
# The `certify_curve` tactic

`certify_curve` closes a goal `HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) ρ` from a *small* description of
a curve: its coefficients, a torsion witness prime, and the point/label functions.  It reads the
`x`-coordinates and labels out of the goal-side data by kernel reduction, computes the
descent-character matrix `matB` and its `𝔽₂` inverse `matM` with the fast helpers in
`ECCompute.CertifyEval`, assembles the `Certificate`, and discharges the referee obligations of
`hasRankGE_of_certificate` in one proof term.

Nothing in `CertifyEval` is trusted: the assembled certificate's obligations (`hB`, `hinv`, …) are
kernel-checked exactly as a hand-written certificate would be, so a wrong matrix only makes the
tactic *fail to close the goal*, never certify a false bound.

```
theorem hasRankGE_example : HasRankGE (toCurveQ 1 0 0 a₄ a₆) 29 := by
  certify_curve coeffs 1 0 0 a₄ a₆ torsion 67 points ptsFn labels labsFn
```
-/

open Lean Elab Tactic Meta Qq

namespace ECCompute

/-- Reduce `e` to a `Nat` value, matching raw literals, `OfNat`, and `Nat.succ`/`Nat.zero`. -/
private partial def getNatE (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if let some n := e.nat? then return n
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => getNatE n
  | (``Nat.succ, #[m]) => return (← getNatE m) + 1
  | (``Nat.zero, _) => return 0
  | _ =>
    if let some n ← getNatValue? e then return n
    throwError "certify_curve: expected a `Nat` literal, got{indentExpr e}"

/-- Reduce `e` to an `Int` value, matching `Int.ofNat`/`Int.negSucc`/`Int.negOfNat`/`Neg.neg`/
`OfNat`. -/
private partial def getIntE (e : Expr) : MetaM Int := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Int.ofNat, #[n]) => return .ofNat (← getNatE n)
  | (``Int.negSucc, #[n]) => return .negSucc (← getNatE n)
  | (``Int.negOfNat, #[n]) => return -(.ofNat (← getNatE n))
  | (``Neg.neg, #[_, _, a]) => return -(← getIntE a)
  | (``OfNat.ofNat, #[_, n, _]) => return .ofNat (← getNatE n)
  | _ =>
    if let some n ← getIntValue? e then return n
    throwError "certify_curve: expected an `Int` literal, got{indentExpr e}"

/-- The `Fin n` literal `⟨i, _⟩` (with `i < n` discharged by `decide`). -/
private def mkFinLit (n i : Nat) : MetaM Expr := do
  let pf ← mkDecideProof (← mkAppM ``LT.lt #[toExpr i, toExpr n])
  mkAppOptM ``Fin.mk #[some (toExpr n), some (toExpr i), some pf]

/-- Syntax of the `certify_curve` tactic; see the module docstring. -/
syntax (name := certifyCurve) "certify_curve" " coeffs " term:max term:max term:max term:max
  term:max " torsion " term:max " points " term:max " labels " term:max : tactic

@[tactic certifyCurve]
def evalCertifyCurve : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_curve coeffs $a1 $a2 $a3 $a4 $a6 torsion $tp points $pts labels $labs) => do
    -- coefficient values (general integral model) and the short-model coefficients
    let ev (s : Term) : TacticM Int := do getIntE (← elabTermEnsuringType s q(Int))
    let v1 ← ev a1; let v2 ← ev a2; let v3 ← ev a3; let v4 ← ev a4
    let sA2 := v1 ^ 2 + 4 * v2
    let sA4 := 16 * v4 + 8 * v1 * v3
    -- `ρ` is the rank bound in the goal `HasRankGE _ ρ`
    let goal ← getMainGoal
    let rho ← getNatE (← goal.getType).appArg!
    -- read the `x`-coordinates (as `num/den`) and the labels `(p, θ)` out of the point/label
    -- functions by kernel reduction
    let ptsFn ← elabTerm pts none
    let labsFn ← elabTerm labs none
    let mut xs : Array (Int × Nat) := #[]
    let mut ls : Array (Nat × Int) := #[]
    for i in [0:rho] do
      let fin ← mkFinLit rho i
      let x ← mkAppM ``Prod.fst #[mkApp ptsFn fin]
      xs := xs.push (← getIntE (← mkAppM ``Rat.num #[x]), ← getNatE (← mkAppM ``Rat.den #[x]))
      let lab := mkApp labsFn fin
      ls := ls.push (← getNatE (← mkAppM ``Prod.fst #[lab]), ← getIntE (← mkAppM ``Prod.snd #[lab]))
    -- the character matrix and its 𝔽₂ inverse (a pure, compiled computation)
    let matB := CertifyEval.computeMatB sA2 sA4 xs.toList ls.toList
    let some matM := CertifyEval.invF2 matB.toArray rho
      | throwError "certify_curve: the descent-character matrix is singular over 𝔽₂"
    let matBStx : Term := quote matB
    let matMStx : Term := quote matM
    let rhoStx : Term := quote rho
    let term ← `(
        let c : Certificate :=
          { a₁ := 0, a₂ := ModelChange.intShortA₂ $a1 $a2, a₃ := 0,
            a₄ := ModelChange.intShortA₄ $a1 $a3 $a4, a₆ := ModelChange.intShortA₆ $a3 $a6,
            rho := $rhoStx, «points» := List.ofFn $pts, «labels» := List.ofFn $labs,
            matB := $matBStx, matM := $matMStx, t := 0, torsionPrime := $tp }
        hasRankGE_of_certificate $a1 $a2 $a3 $a4 $a6 c $pts $labs
        rfl
        (by intro i; fin_cases i <;> (rw [WeierstrassCurve.Affine.equation_iff]; simp only [$pts:term, ModelChange.intShortA₂, ModelChange.intShortA₄, ModelChange.intShortA₆, curve, mk'_eq_div]; decide +kernel))
        (by intro j; fin_cases j <;> exact Nat.prime_of_passes _ (by decide) (by decide) (by quickRfl))
        (by intro j; fin_cases j <;> quickRfl)
        (checkB_true (by quickRfl))
        (by quickRfl)
        rfl (by decide)
        (by rw [← Bool.not_eq_true', ← Bool.not'_eq_not]; quickRfl))
    let e ← elabTermEnsuringType term (← goal.getType)
    Term.synthesizeSyntheticMVarsNoPostponing
    goal.assign (← instantiateMVars e)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end ECCompute
