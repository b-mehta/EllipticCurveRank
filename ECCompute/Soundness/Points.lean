/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import ECCompute.Soundness.Fold

/-!
# Soundness of the point-on-curve checks

`checkPoint_iff`/`checkPoints_iff` and `checkPointShort_iff`/`checkPointsShort_iff` relate the
kernel point checks from `Kernel` to the affine Weierstrass equation, at a single point and at every
point of a list, for the full model `⟨a₁, a₂, a₃, a₄, a₆⟩` and the short model `⟨0, a₂, 0, a₄, a₆⟩`.
`checkPointsShort` runs the `Nat` check `checkPointShortNat`, related to the `Int` `checkPointShort`
by `checkPointShortNat_eq`.
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

/-- The sign-split `Nat` point check computes the same `Bool` as the `Int` check: the coefficient
magnitudes and signs `(a.natAbs, intSignNeg a)` reconstruct each signed term of the Weierstrass
identity. Casing every coordinate's sign leaves a polynomial identity per case. -/
theorem checkPointShortNat_eq {x y : ℚ} :
    checkPointShortNat a₂.natAbs a₄.natAbs a₆.natAbs (intSignNeg a₂) (intSignNeg a₄) (intSignNeg a₆)
        x y = checkPointShort a₂ a₄ a₆ x y := by
  rcases a₂ with n₂ | n₂ <;> rcases a₄ with n₄ | n₄ <;> rcases a₆ with n₆ | n₆ <;>
    rcases hx : x.num with xn | xn <;> rcases hy : y.num with yn | yn <;>
    simp only [checkPointShortNat, checkPointShort, intSignNeg, Int.natAbs, Bool.not',
      Nat.mul_eq, Nat.add_eq, Int.mul_def, Int.add_def, hx, hy] <;>
    rw [Bool.eq_iff_iff, Nat.beq_eq, Int.beq'_eq, ← Nat.cast_inj (R := ℤ)] <;>
    push_cast [Int.negSucc_eq] <;>
    constructor <;> intro h <;> linear_combination h

/-- `checkPointsShort` holds iff every listed point satisfies the short-model equation. -/
public theorem checkPointsShort_iff {pts : List (ℚ × ℚ)} :
    checkPointsShort a₂ a₄ a₆ pts ↔
      ∀ p ∈ pts, (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation p.1 p.2 := by
  simp only [checkPointsShort, allList_iff, checkPointShortNat_eq, checkPointShort_iff]

end ECCompute
