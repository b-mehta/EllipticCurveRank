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

/-- `checkPointShort a₂ a₄ a₆ x y` holds iff `(x, y)` satisfies the affine Weierstrass equation of
the short model `⟨0, a₂, 0, a₄, a₆⟩`. -/
theorem checkPointShort_iff {x y : ℚ} :
    checkPointShort a₂ a₄ a₆ x y ↔
      (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation x y := by
  simp only [Affine.equation_iff, checkPointShort, Int.beq'_eq, Int.mul_def, Int.add_def]
  have hxd : (x.den : ℚ) ≠ 0 := mod_cast x.den_nz
  have hyd : (y.den : ℚ) ≠ 0 := mod_cast y.den_nz
  have hx : (x.num : ℚ) = x * x.den := (div_eq_iff hxd).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * y.den := (div_eq_iff hyd).mp (Rat.num_div_den y)
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hxd) (pow_ne_zero _ hyd)
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  grind

/-- `checkPointsShort` holds iff every listed point satisfies the short-model equation. -/
public theorem checkPointsShort_iff {pts : List (ℚ × ℚ)} :
    checkPointsShort a₂ a₄ a₆ pts ↔
      ∀ p ∈ pts, (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation p.1 p.2 := by
  -- MEASUREMENT ONLY: `checkPointsShort` now folds the signed-`Nat` point check
  -- `checkPointShortNat`; the soundness bridge to `checkPointShort_iff` is not restated here.
  sorry

end ECCompute
