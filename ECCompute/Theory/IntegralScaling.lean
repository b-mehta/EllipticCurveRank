/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model

public import ECCompute.Theory.CompleteSquare

/-!
# The general-to-integer-short-model change of variables

The certified rank bound (`ECCompute.rank_ge_of_certificate`) lives on the integer short model
`curve A₂ A₄ A₆` (`y² = x³ + A₂x² + A₄x + A₆`, `Aᵢ : ℤ`), where the descent character `lambda`
is defined. A general integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`
(`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`) must be carried to it. `CompleteSquare.pointAddEquiv`
completes the square to a *rational*-coefficient short model; this file scales it to the integer
short model by the change of variables `⟨1/2, 0, 0, 0⟩`.

The change of variables `⟨1/2, 0, -a₁/2, -a₃/2⟩` carries `⟨a₁, a₂, a₃, a₄, a₆⟩` to the integral
short model `curve b₂ (8·b₄) (16·b₆)`, with `b`-invariants `b₂ = a₁² + 4a₂`, `b₄ = 2a₄ + a₁a₃`,
`b₆ = a₃² + 4a₆`:

* `A₂ = a₁² + 4a₂`  (`= b₂`),
* `A₄ = 16a₄ + 8a₁a₃`  (`= 8·b₄`),
* `A₆ = 64a₆ + 16a₃²`  (`= 16·b₆`).

## Main results

* `IntegralScaling.scaling`: the pure scaling `⟨1/v, 0, 0, 0⟩`, whose action is `(x, y) ↦
  (v²x, v³y)`.
* `IntegralScaling.intShortModel`: the integral short model of a general integral Weierstrass
  curve over `ℚ`.
* `IntegralScaling.generalToShortEquiv`: the composite `⟨1/2, 0, -a₁/2, -a₃/2⟩` change of
  variables, a group isomorphism from the general model to its integral short model.
-/

namespace ECCompute.IntegralScaling

open WeierstrassCurve WeierstrassCurve.Affine CompleteSquare

/-- The pure scaling change of variables `⟨1/v, 0, 0, 0⟩` (`v ≠ 0`), whose action `C • W` scales the
coefficients by `W.aᵢ ↦ vⁱ · W.aᵢ` and points by `(x, y) ↦ (v²x, v³y)`. -/
public def scaling (v : ℚ) (hv : v ≠ 0) : VariableChange ℚ := ⟨(Units.mk0 v hv)⁻¹, 0, 0, 0⟩

/-! ## The integral short model and the change of variables -/

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
