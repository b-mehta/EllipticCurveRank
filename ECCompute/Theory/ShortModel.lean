/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.VariableChangePoint
public import ECCompute.Theory.Model

/-!
# The general curve to the integral short model

The certified rank bound lives on the integral short model `curve A₂ A₄ A₆`
(`y² = x³ + A₂x² + A₄x + A₆`, `Aᵢ : ℤ`), where the descent character is defined. A general integral
Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩` is carried to it in two steps, each a group isomorphism of
Mordell-Weil groups (so a rank lower bound transfers back):

* completing the square, `⟨1, 0, -a₁/2, -a₃/2⟩`, to a *rational* short model `shortModel W`
  (`CompleteSquare.pointAddEquiv`);
* scaling by `v = 2`, `⟨1/2, 0, 0, 0⟩`, to the integral short model
  (`IntegralScaling.generalToShortEquiv`).

## Main results

* `CompleteSquare.shortModel`, `CompleteSquare.pointAddEquiv`: the rational short model and its
  group isomorphism to the general model.
* `IntegralScaling.intShortModel`, `IntegralScaling.generalToShortEquiv`: the integral short model
  and the composite group isomorphism to it.
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
theorem shortModel_a₁ : (shortModel W).a₁ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₁]

@[simp]
theorem shortModel_a₂ : (shortModel W).a₂ = W.a₂ + W.a₁ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₂, inv_one, Units.val_one, one_pow]

@[simp]
theorem shortModel_a₃ : (shortModel W).a₃ = 0 := by
  grind [shortModel, completeSquare, variableChange_a₃]

@[simp]
theorem shortModel_a₄ : (shortModel W).a₄ = W.a₄ + W.a₁ * W.a₃ / 2 := by
  grind [shortModel, completeSquare, variableChange_a₄, inv_one, Units.val_one, one_pow]

@[simp]
theorem shortModel_a₆ : (shortModel W).a₆ = W.a₆ + W.a₃ ^ 2 / 4 := by
  grind [shortModel, completeSquare, variableChange_a₆, inv_one, Units.val_one, one_pow]

/-- The completing-the-square change of variables induces a group isomorphism between the
Mordell-Weil groups of the general model `W` and the short model `shortModel W`, so any rank lower
bound on the short model transfers back. -/
public def pointAddEquiv (W : WeierstrassCurve ℚ) :
    W.toAffine.Point ≃+ (shortModel W).toAffine.Point :=
  VariableChange.pointAddEquiv (completeSquare W)

end ECCompute.CompleteSquare

end

namespace ECCompute.IntegralScaling

open WeierstrassCurve WeierstrassCurve.Affine CompleteSquare

/-! ## The integral short model and the scaling change of variables -/

/-- The pure scaling change of variables `⟨1/v, 0, 0, 0⟩` (`v ≠ 0`), whose action `C • W` scales the
coefficients by `W.aᵢ ↦ vⁱ · W.aᵢ` and points by `(x, y) ↦ (v²x, v³y)`. -/
public def scaling (v : ℚ) (hv : v ≠ 0) : VariableChange ℚ := ⟨(Units.mk0 v hv)⁻¹, 0, 0, 0⟩

/-- The `a₂` coefficient of the integral short model: `A₂ = a₁² + 4a₂ = b₂`. -/
@[expose] public def intShortA₂ (a₁ a₂ : ℤ) : ℤ := a₁ ^ 2 + 4 * a₂

/-- The `a₄` coefficient of the integral short model: `A₄ = 16a₄ + 8a₁a₃ = 8·b₄`. -/
@[expose] public def intShortA₄ (a₁ a₃ a₄ : ℤ) : ℤ := 16 * a₄ + 8 * a₁ * a₃

/-- The `a₆` coefficient of the integral short model: `A₆ = 64a₆ + 16a₃² = 16·b₆`. -/
@[expose] public def intShortA₆ (a₃ a₆ : ℤ) : ℤ := 64 * a₆ + 16 * a₃ ^ 2

/-- The integral short model `curve (a₁²+4a₂) (16a₄+8a₁a₃) (64a₆+16a₃²)` associated to the general
integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
@[expose] public def intShortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  curve (a₁ ^ 2 + 4 * a₂) (16 * a₄ + 8 * a₁ * a₃) (64 * a₆ + 16 * a₃ ^ 2)

/-- Scaling the rational short model by `v = 2` produces the integral short model. -/
public theorem scaling_smul_shortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    scaling 2 two_ne_zero • shortModel (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ)
      = intShortModel a₁ a₂ a₃ a₄ a₆ := by
  ext <;>
    simp only [scaling, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, shortModel_a₁, shortModel_a₂, shortModel_a₃,
      shortModel_a₄, shortModel_a₆, intShortModel, curve, inv_inv, Units.val_mk0] <;>
    push_cast <;> ring

/-- The composite change of variables `⟨1/2, 0, -a₁/2, -a₃/2⟩` (complete the square, then scale by
`v = 2`) is a group isomorphism from the general model `⟨a₁, a₂, a₃, a₄, a₆⟩` to its integral short
model `scaling 2 • shortModel ⟨a₁, a₂, a₃, a₄, a₆⟩` (equal to `intShortModel a₁ a₂ a₃ a₄ a₆` by
`scaling_smul_shortModel`), on which the descent character is stated. -/
public def generalToShortEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Point ≃+
      (scaling 2 two_ne_zero
          • shortModel (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ)).toAffine.Point :=
  (pointAddEquiv ⟨a₁, a₂, a₃, a₄, a₆⟩).trans (VariableChange.pointAddEquiv (scaling 2 two_ne_zero))

end ECCompute.IntegralScaling
