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

`checkPoints_iff` shows that the kernel check `ECCompute.checkPoints` (from `Kernel`) over the flat
point encoding `(xnA, xs, xd, ynA, yd)` holds exactly when every decoded point satisfies the affine
Weierstrass equation of the short model `⟨0, a₂, 0, a₄, a₆⟩` and is in lowest terms with positive
denominators (the reduced form the descent character relies on).
-/

namespace ECCompute

open WeierstrassCurve

variable {a₂ a₄ a₆ : ℤ}

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
  simp only [checkPointShortNat, Nat.beq_eq]
  rw [← Nat.cast_inj (R := ℤ)]
  cases a₂ <;> cases a₄ <;> cases a₆ <;> cases sx <;>
    simp only [intSignNeg, Int.natAbs_ofNat', Int.natAbs_negSucc, Nat.succ_eq_add_one,
      Bool.not_true, Bool.not_false] <;>
    simp only [Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.mul_eq, Nat.add_eq] <;>
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
    (intId_iff_equation (by exact mod_cast hxd.ne') (by exact mod_cast hyd.ne'))

/-- `checkPoints` holds iff every listed point, decoded from its flat `(xnA, xs, xd, ynA, yd)`
encoding, satisfies the short-model equation and is in lowest terms with positive denominators (the
reduced form the descent character relies on). -/
public theorem checkPoints_iff {pts : List (ℕ × Bool × ℕ × ℕ × ℕ)} :
    checkPoints a₂ a₄ a₆ pts ↔
      ∀ p ∈ pts, ((⟨0, a₂, 0, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation
          ((if p.2.1 then -(p.1 : ℚ) else (p.1 : ℚ)) / (p.2.2.1 : ℚ))
          ((p.2.2.2.1 : ℚ) / (p.2.2.2.2 : ℚ)) ∧
        p.1.Coprime p.2.2.1 ∧ 0 < p.2.2.1 ∧ p.2.2.2.1.Coprime p.2.2.2.2 ∧ 0 < p.2.2.2.2) := by
  rw [checkPoints, allList_iff]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  obtain ⟨xn, sx, xd, yn, yd⟩ := p
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.Coprime]
  constructor
  · rintro ⟨hchk, ⟨hcx, hdx⟩, hcy, hdy⟩
    exact ⟨(checkPointShortNat_iff hdx hdy).mp hchk, hcx, hdx, hcy, hdy⟩
  · rintro ⟨heq, hcx, hdx, hcy, hdy⟩
    exact ⟨(checkPointShortNat_iff hdx hdy).mpr heq, ⟨hcx, hdx⟩, hcy, hdy⟩

/-- The decoded `x`-coordinate `(if sx then -xn else xn) / xd` as a quotient of integers. -/
theorem decode_eq {xn xd : ℕ} {sx : Bool} :
    (if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)
      = ((if sx then -(xn : ℤ) else (xn : ℤ) : ℤ) : ℚ) / ((xd : ℤ) : ℚ) := by
  cases sx <;> push_cast <;> ring

/-- The signed `x` numerator and `xd` are coprime when `xn` and `xd` are. -/
theorem decode_coprime {xn xd : ℕ} {sx : Bool} (hcx : xn.Coprime xd) :
    (if sx then -(xn : ℤ) else (xn : ℤ)).natAbs.Coprime (xd : ℤ).natAbs := by
  cases sx <;> simpa [Int.natAbs_neg] using hcx

/-- The decoded `x`-coordinate of a reduced flat point has signed numerator `if sx then -xn else xn`. -/
public theorem decode_num {xn xd : ℕ} {sx : Bool} (hcx : xn.Coprime xd) (hdx : 0 < xd) :
    ((if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)).num = if sx then -(xn : ℤ) else (xn : ℤ) := by
  rw [decode_eq, Rat.num_div_eq_of_coprime (by exact mod_cast hdx) (decode_coprime hcx)]

/-- The decoded `x`-coordinate of a reduced flat point has denominator `xd`. -/
public theorem decode_den {xn xd : ℕ} {sx : Bool} (hcx : xn.Coprime xd) (hdx : 0 < xd) :
    ((if sx then -(xn : ℚ) else (xn : ℚ)) / (xd : ℚ)).den = xd := by
  rw [decode_eq]
  exact mod_cast Rat.den_div_eq_of_coprime (by exact mod_cast hdx)
    (a := if sx then -(xn : ℤ) else (xn : ℤ)) (decode_coprime hcx)

end ECCompute
