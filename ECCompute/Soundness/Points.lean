/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.CompleteSquare
public import ECCompute.Soundness.Fold

/-!
# Soundness of the point-on-curve check

`checkPoint_iff` and `checkPoints_iff` show that the kernel checks `ECCompute.checkPoint` and
`ECCompute.checkPoints` (from `Kernel`) hold exactly when the point, respectively every point
in a list, satisfies the affine Weierstrass equation of the model `⟨a₁, a₂, a₃, a₄, a₆⟩`.
-/

namespace ECCompute

open WeierstrassCurve

variable {a₁ a₂ a₃ a₄ a₆ : ℤ}

/-- `checkPoint a₁ a₂ a₃ a₄ a₆ x y` holds iff `(x, y)` satisfies the affine Weierstrass equation of
the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
theorem checkPoint_iff {x y : ℚ} :
    checkPoint a₁ a₂ a₃ a₄ a₆ x y ↔
      (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation x y := by
  simp only [Affine.equation_iff, checkPoint, Int.beq'_eq, Int.mul_def, Int.add_def]
  have hxd : (x.den : ℚ) ≠ 0 := mod_cast x.den_nz
  have hyd : (y.den : ℚ) ≠ 0 := mod_cast y.den_nz
  have hx : (x.num : ℚ) = x * x.den := (div_eq_iff hxd).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * y.den := (div_eq_iff hyd).mp (Rat.num_div_den y)
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hxd) (pow_ne_zero _ hyd)
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  grind

/-- `checkPoints` holds iff every listed point satisfies the equation. -/
public theorem checkPoints_iff {pts : List (ℚ × ℚ)} :
    checkPoints a₁ a₂ a₃ a₄ a₆ pts ↔
      ∀ p ∈ pts, (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation p.1 p.2 := by
  simp only [checkPoints, allList_iff, checkPoint_iff]

end ECCompute
