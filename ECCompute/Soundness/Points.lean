/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import ECCompute.Soundness.Fold

/-!
# Soundness of the point-on-curve check

`checkPoint_iff` and `checkPoints_iff` show that the kernel checks
`ECCompute.checkPoint` and `ECCompute.checkPoints` (from `Kernel`) hold exactly when the
point, respectively every point in a list, satisfies the affine Weierstrass equation of the short
model `curveQ a₂ a₄ a₆`.
-/

namespace ECCompute

open WeierstrassCurve

variable {a₂ a₄ a₆ : ℤ}

/-- `checkPoint a₂ a₄ a₆ x y` holds iff `(x, y)` satisfies the affine Weierstrass equation of
the short model `curveQ a₂ a₄ a₆`. -/
theorem checkPoint_iff {x y : ℚ} :
    checkPoint a₂ a₄ a₆ x y ↔ (curveQ a₂ a₄ a₆).toAffine.Equation x y := by
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 := by positivity
  simp only [checkPoint, Int.beq'_eq, ← Int.cast_inj (α := ℚ), Int.mul_def, Int.cast_mul,
    Int.add_def, Int.cast_add, baseChange, curve, Affine.equation_iff]
  grind [Rat.mul_den_eq_num, Int.cast_natCast, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast]

/-- `checkPoints` holds iff every listed point satisfies the short-model equation. -/
public theorem checkPoints_iff {pts : List (ℚ × ℚ)} :
    checkPoints a₂ a₄ a₆ pts ↔ ∀ p ∈ pts, (curveQ a₂ a₄ a₆).toAffine.Equation p.1 p.2 := by
  grind [checkPoints, checkPoint_iff]

end ECCompute
