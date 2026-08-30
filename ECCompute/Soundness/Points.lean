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

/-- The flat-`Nat` point check equals the cleared integer Weierstrass identity of the short model,
with the `x` numerator recovered from its magnitude `xn` and sign `sx`. -/
theorem checkPointShortNat_intId {xn : ℕ} {sx : Bool} {xd yn yd : ℕ} :
    checkPointShortNat a₂.natAbs a₄.natAbs a₆.natAbs (intSignNeg a₂) (intSignNeg a₄)
        (intSignNeg a₆) xn sx xd yn yd = true ↔
      (yn : ℤ) ^ 2 * (xd : ℤ) ^ 3 =
        (if sx then -(xn : ℤ) else (xn : ℤ)) ^ 3 * (yd : ℤ) ^ 2 +
          a₂ * (if sx then -(xn : ℤ) else (xn : ℤ)) ^ 2 * (xd : ℤ) * (yd : ℤ) ^ 2 +
          a₄ * (if sx then -(xn : ℤ) else (xn : ℤ)) * (xd : ℤ) ^ 2 * (yd : ℤ) ^ 2 +
          a₆ * (xd : ℤ) ^ 3 * (yd : ℤ) ^ 2 := by
  simp only [checkPointShortNat, Bool.rec_eq, Nat.beq_eq]
  rw [← Nat.cast_inj (R := ℤ)]
  cases a₂ <;> cases a₄ <;> cases a₆ <;> cases sx <;>
    simp only [intSignNeg, Int.natAbs_ofNat, Int.natAbs_ofNat', Int.natAbs_negSucc,
      Bool.not'_eq_not, Bool.not_true, Bool.not_false, reduceIte, ite_true, ite_false,
      if_true, if_false, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.succ_eq_add_one] <;>
    push_cast <;>
    constructor <;> intro h <;> linear_combination h

/-- The cleared integer Weierstrass identity of the short model is exactly the affine equation at
the decoded rational point, once both denominators are nonzero. -/
theorem intId_iff_equation {xn : ℕ} {sx : Bool} {xd yn yd : ℕ}
    (hxdQ : (xd : ℚ) ≠ 0) (hydQ : (yd : ℚ) ≠ 0) :
    ((yn : ℤ) ^ 2 * (xd : ℤ) ^ 3 =
        (if sx then -(xn : ℤ) else (xn : ℤ)) ^ 3 * (yd : ℤ) ^ 2 +
          a₂ * (if sx then -(xn : ℤ) else (xn : ℤ)) ^ 2 * (xd : ℤ) * (yd : ℤ) ^ 2 +
          a₄ * (if sx then -(xn : ℤ) else (xn : ℤ)) * (xd : ℤ) ^ 2 * (yd : ℤ) ^ 2 +
          a₆ * (xd : ℤ) ^ 3 * (yd : ℤ) ^ 2) ↔
      (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation
        ((if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)) ((yn : ℚ) / (yd : ℚ)) := by
  simp only [Affine.equation_iff]
  have hx : (if sx then -(xn : ℚ) else (xn : ℚ))
      = ((if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)) * (xd : ℚ) :=
    (div_mul_cancel₀ _ hxdQ).symm
  have hy : (yn : ℚ) = ((yn : ℚ) / (yd : ℚ)) * (yd : ℚ) := (div_mul_cancel₀ _ hydQ).symm
  have hD : (xd : ℚ) ^ 3 * (yd : ℚ) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hxdQ) (pow_ne_zero _ hydQ)
  rw [← Int.cast_inj (α := ℚ)]
  push_cast [apply_ite ((↑) : ℤ → ℚ)]
  grind

/-- The flat-`Nat` point check holds, for a point with positive denominators, exactly when the
decoded rational point satisfies the short-model equation. -/
theorem checkPointShortNat_iff {xn : ℕ} {sx : Bool} {xd yn yd : ℕ} (hxd : 0 < xd) (hyd : 0 < yd) :
    checkPointShortNat a₂.natAbs a₄.natAbs a₆.natAbs (intSignNeg a₂) (intSignNeg a₄)
        (intSignNeg a₆) xn sx xd yn yd = true ↔
      (⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation
        ((if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)) ((yn : ℚ) / (yd : ℚ)) :=
  checkPointShortNat_intId.trans
    (intId_iff_equation (by exact_mod_cast hxd.ne') (by exact_mod_cast hyd.ne'))

/-- `checkPointsShort` holds iff every listed point, decoded from its flat `(xnA, xs, xd, ynA, yd)`
encoding, satisfies the short-model equation and is in lowest terms with positive denominators (the
reduced form the descent character relies on). -/
public theorem checkPointsShort_iff {pts : List (ℕ × Bool × ℕ × ℕ × ℕ)} :
    checkPointsShort a₂ a₄ a₆ pts ↔
      ∀ p ∈ pts, ((⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation
          ((if p.2.1 then -(p.1 : ℚ) else (p.1 : ℚ)) / (p.2.2.1 : ℚ))
          ((p.2.2.2.1 : ℚ) / (p.2.2.2.2 : ℚ)) ∧
        p.1.Coprime p.2.2.1 ∧ 0 < p.2.2.1 ∧ p.2.2.2.1.Coprime p.2.2.2.2 ∧ 0 < p.2.2.2.2) := by
  rw [checkPointsShort, allList_iff]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  obtain ⟨xn, sx, xd, yn, yd⟩ := p
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.Coprime]
  constructor
  · rintro ⟨hchk, ⟨hcx, hdx⟩, hcy, hdy⟩
    exact ⟨(checkPointShortNat_iff hdx hdy).mp hchk, hcx, hdx, hcy, hdy⟩
  · rintro ⟨heq, hcx, hdx, hcy, hdy⟩
    exact ⟨(checkPointShortNat_iff hdx hdy).mpr heq, ⟨hcx, hdx⟩, hcy, hdy⟩

end ECCompute
