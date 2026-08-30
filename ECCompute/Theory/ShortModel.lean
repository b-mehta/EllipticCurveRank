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
-/

namespace ECCompute.IntegralScaling

open WeierstrassCurve

/-- The pure scaling change of variables `⟨1/v, 0, 0, 0⟩` (`v ≠ 0`), whose action `C • W` scales the
coefficients by `W.aᵢ ↦ vⁱ · W.aᵢ` and points by `(x, y) ↦ (v²x, v³y)`. -/
@[expose] public def scaling (v : ℚ) (hv : v ≠ 0) : VariableChange ℚ :=
  ⟨(Units.mk0 v hv)⁻¹, 0, 0, 0⟩

end ECCompute.IntegralScaling
