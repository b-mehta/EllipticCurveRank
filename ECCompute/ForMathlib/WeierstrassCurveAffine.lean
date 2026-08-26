/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Negation on Weierstrass curves with `a₁ = a₃ = 0`

For a Weierstrass curve `W` with `W.a₁ = 0` and `W.a₃ = 0`, the negation map `negY` on affine
points is `y ↦ -y`.

## Main results

* `WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero`: `negY x y = -y` when `a₁ = a₃ = 0`.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]

/-- On a Weierstrass curve with `a₁ = a₃ = 0`, negation is `negY x y = -y`. -/
@[grind =]
theorem negY_of_a₁_a₃_eq_zero (W : WeierstrassCurve R) (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    (x y : R) : W.toAffine.negY x y = -y := by simp [negY, ha1, ha3]

end WeierstrassCurve.Affine
