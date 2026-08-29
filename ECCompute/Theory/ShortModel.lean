/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The integral short model

The certified rank bound lives on the integral short model `curveQ A₂ A₄ A₆`
(`y² = x³ + A₂x² + A₄x + A₆`, `Aᵢ : ℤ`), where the descent character is defined. A general integral
Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩` reaches it by completing the square
(`WeierstrassCurve.toCharNeTwoNF`) and then scaling by `v = 2`; that transport is carried out in
`ECCompute.hasRankGE_of_certificate`.

## Main declarations

* `ECCompute.IntegralScaling.scaling`: the scaling change of variables `⟨1/v, 0, 0, 0⟩`.
* `ECCompute.IntegralScaling.intShortModel`: the integral short model of `⟨a₁, a₂, a₃, a₄, a₆⟩`.
-/

namespace ECCompute.IntegralScaling

open WeierstrassCurve

/-- The pure scaling change of variables `⟨1/v, 0, 0, 0⟩` (`v ≠ 0`), whose action `C • W` scales the
coefficients by `W.aᵢ ↦ vⁱ · W.aᵢ` and points by `(x, y) ↦ (v²x, v³y)`. -/
@[expose] public def scaling (v : ℚ) (hv : v ≠ 0) : VariableChange ℚ :=
  ⟨(Units.mk0 v hv)⁻¹, 0, 0, 0⟩

/-- The `a₂` coefficient of the integral short model: `A₂ = a₁² + 4a₂ = b₂`. -/
@[expose] public def intShortA₂ (a₁ a₂ : ℤ) : ℤ := a₁ ^ 2 + 4 * a₂

/-- The `a₄` coefficient of the integral short model: `A₄ = 16a₄ + 8a₁a₃ = 8·b₄`. -/
@[expose] public def intShortA₄ (a₁ a₃ a₄ : ℤ) : ℤ := 16 * a₄ + 8 * a₁ * a₃

/-- The `a₆` coefficient of the integral short model: `A₆ = 64a₆ + 16a₃² = 16·b₆`. -/
@[expose] public def intShortA₆ (a₃ a₆ : ℤ) : ℤ := 64 * a₆ + 16 * a₃ ^ 2

/-- The integral short model `curveQ (a₁²+4a₂) (16a₄+8a₁a₃) (64a₆+16a₃²)` associated to the general
integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
@[expose] public def intShortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  curveQ (a₁ ^ 2 + 4 * a₂) (16 * a₄ + 8 * a₁ * a₃) (64 * a₆ + 16 * a₃ ^ 2)

end ECCompute.IntegralScaling
