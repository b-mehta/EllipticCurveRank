/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.VariableChangePoint

/-!
# The completing-the-square model isomorphism

Over `ℚ` (characteristic `≠ 2`) the substitution `y ↦ y - (a₁x + a₃)/2` (the change of variables
`⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩`) carries a general Weierstrass model `W` to a short model
`y² = x³ + a₂'x² + a₄'x + a₆'`, on which the descent character is stated. Rank is an isomorphism
invariant, so a rank lower bound on the short model transfers back; see `pointAddEquiv`.

The point-on-curve check `checkPoint`/`checkPoints` used alongside this isomorphism lives in
`ECCompute.Kernel`.

## Main results

* `CompleteSquare.completeSquare`, `CompleteSquare.shortModel`: the
  `⟨1, 0, -a₁/2, -a₃/2⟩` change of variables and the resulting short model
  `y² = x³ + a₂'x² + a₄'x + a₆'`.
* `CompleteSquare.pointAddEquiv`: this change of variables as a group isomorphism `W.Point ≃+
  (shortModel W).Point`, so a rank lower bound transfers between the two models.
-/

section

namespace ECCompute.CompleteSquare

open WeierstrassCurve

/-! ## The completing-the-square model isomorphism -/

/-- The change of variables `⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩` completing the square for a curve
`W`: the substitution `y ↦ y - (W.a₁ x + W.a₃)/2` (over `ℚ`, where `2` is invertible) that clears
the `a₁` and `a₃` coefficients. -/
def completeSquare (W : WeierstrassCurve ℚ) : VariableChange ℚ := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩

/-- The short model `y² = x³ + a₂'x² + a₄'x + a₆'` obtained from `W` by completing the square. Its
`a₁` and `a₃` coefficients vanish (`shortModel_a₁`, `shortModel_a₃`). -/
public def shortModel (W : WeierstrassCurve ℚ) : WeierstrassCurve ℚ := completeSquare W • W

variable {W : WeierstrassCurve ℚ}

@[simp]
public theorem shortModel_a₁ : (shortModel W).a₁ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₁]

@[simp]
public theorem shortModel_a₂ : (shortModel W).a₂ = W.a₂ + W.a₁ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₂, inv_one, Units.val_one, one_pow]

@[simp]
public theorem shortModel_a₃ : (shortModel W).a₃ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₃]

@[simp]
public theorem shortModel_a₄ : (shortModel W).a₄ = W.a₄ + W.a₁ * W.a₃ / 2 := by
  grind [shortModel, completeSquare, variableChange_a₄, inv_one, Units.val_one, one_pow]

@[simp]
public theorem shortModel_a₆ : (shortModel W).a₆ = W.a₆ + W.a₃ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₆, inv_one, Units.val_one, one_pow]

/-- The completing-the-square change of variables induces a group isomorphism between the
Mordell-Weil groups of the general model `W` and the short model `shortModel W`, so any rank lower
bound on the short model transfers back. -/
public def pointAddEquiv (W : WeierstrassCurve ℚ) :
    W.toAffine.Point ≃+ (shortModel W).toAffine.Point :=
  VariableChange.variableChangePointEquiv (completeSquare W)

end ECCompute.CompleteSquare

end
