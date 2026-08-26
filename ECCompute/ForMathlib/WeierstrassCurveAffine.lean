/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Affine point lemmas for Weierstrass curves

The curve equation of a nonsingular affine point, and the negation map `negY` as `y ↦ -y` on a
Weierstrass curve with `a₁ = a₃ = 0`.

## Main results

* `WeierstrassCurve.Affine.Nonsingular.equation`: a nonsingular point satisfies the curve
  equation.
* `WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero`: `negY x y = -y` when `a₁ = a₃ = 0`.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]

/-- A nonsingular point satisfies the curve equation. -/
theorem Nonsingular.equation {W : WeierstrassCurve R} {x y : R}
    (h : W.toAffine.Nonsingular x y) : W.toAffine.Equation x y := h.1

/-- On a Weierstrass curve with `a₁ = a₃ = 0`, negation is `negY x y = -y`. -/
@[grind =]
theorem negY_of_a₁_a₃_eq_zero (W : WeierstrassCurve R) (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    (x y : R) : W.toAffine.negY x y = -y := by
  simp [negY, ha1, ha3]

end WeierstrassCurve.Affine
