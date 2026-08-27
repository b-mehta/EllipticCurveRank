/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import ECCompute.ForMathlib.RatDenom
public import ECCompute.Theory.Descent.ReductionMap
import ECCompute.Theory.Descent.PointArith
import ECCompute.ForMathlib.WeierstrassCurve
import Mathlib.Tactic.Qify

/-!
# Additivity of the reduction map

The reduction map `redP : E(ℚ) → E(𝔽ₚ)` (from `Descent.ReductionMap`) is an additive
homomorphism. The proof runs in three stages: the group-law denominators survive reduction
(`reduced_slope_eq`, `reduced_addX_eq`, `reduced_addY_eq`); the kernel of reduction is closed
under the group law (`den_addX_both_kernel`); and the full case analysis on the affine group law
assembles these into `redP_map_add`, packaged as the homomorphism `redHom`.

## Main declarations

* `ECCompute.redP_map_add`: `redP` preserves the group law.
* `ECCompute.redHom`: `redP` as an `AddMonoidHom E(ℚ) → E(𝔽ₚ)`.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

/-! ## Denominators of the group law survive reduction -/

section
open Rat

variable {x₁ y₁ x₂ y₂ : ℚ}

section
variable [Fact p.Prime]

/-! ### The reduced secant slope -/

/-- The secant numerator `x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄` has good denominator, and its
reduction is the corresponding polynomial in `X̄₁, X̄₂`. -/
theorem cast_secant_num (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0) :
    ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄).den : ZMod p) ≠ 0
      ∧ ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ : ℚ) : ZMod p)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
  have hx1sq : ((x₁ ^ 2 : ℚ).den : ZMod p) ≠ 0 := den_pow_ne_zero Fact.out hd1 2
  have hx2sq : ((x₂ ^ 2 : ℚ).den : ZMod p) ≠ 0 := den_pow_ne_zero Fact.out hd2 2
  have hprod : ((x₁ * x₂ : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out hd1 hd2
  have esum : ((x₁ + x₂ : ℚ).den : ZMod p) ≠ 0 := den_add_ne_zero Fact.out hd1 hd2
  have e1 := den_add_ne_zero Fact.out hx1sq hprod
  have e2 := den_add_ne_zero Fact.out e1 hx2sq
  have e3 : ((a₂ * (x₁ + x₂)).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out (by simp) esum
  have e4 := den_add_ne_zero Fact.out e2 e3
  refine ⟨den_add_ne_zero Fact.out e4 (by simp), ?_⟩
  simp [cast_add_of_ne_zero, cast_mul_of_ne_zero, *]

/-- For the reduced secant slope, `slope·(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄`. -/
theorem slope_mul_add_eq (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂) :
    (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂)
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
  have hℓ : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    grind [Affine.slope_of_X_ne]
  grind

/-- The reduced secant slope is well-defined. When `X̄₁ = X̄₂` but `x₁ ≠ x₂` over `ℚ` and the
reduced point is not `2`-torsion (`Ȳ₁ + Ȳ₂ ≠ 0`), the standard slope `(y₁ - y₂)/(x₁ - x₂)` (a
`0/0` mod `p`) equals the alternate form `(x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄)/(y₁ + y₂)`, whose
denominator survives reduction. -/
theorem reduced_slope_den (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hy2 : (y₁ : ZMod p) + y₂ ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← cast_add_of_ne_zero hdy1 hdy2, h0, cast_zero]
  have halt : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]; exact slope_mul_add_eq hne h₁ h₂
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by rwa [cast_add_of_ne_zero hdy1 hdy2]
  have hinv : ((y₁ + y₂ : ℚ)⁻¹.den : ZMod p) ≠ 0 := by
    rw [Rat.den_inv_of_ne_zero hy12, ne_eq, ZMod.natCast_eq_zero_iff, ← Int.natCast_dvd_natCast,
      Int.dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h ↦ hy2' (by rw [Rat.cast_def, h, zero_div])
  rw [halt, div_eq_mul_inv]
  exact den_mul_ne_zero Fact.out (cast_secant_num hd1 hd2).1 hinv

/-- The reduced coordinates satisfy the reduced `addX` relation `S² = X̄₃ + a₂ + X̄₁ + X̄₂` and the
alternate-slope identity `S·(Ȳ₁ + Ȳ₂) = X̄₁² + X̄₁X̄₂ + X̄₂² + a₂(X̄₁ + X̄₂) + a₄`, for the reduced
secant slope `S = (slope …)`. -/
theorem reduced_tangent_eqs (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hℓden : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) ^ 2
        = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)
          + a₂ + x₁ + x₂
      ∧ ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := curve_addX
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₂ + x₁ + x₂ := by grind
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rwa [cast_pow,
      cast_add_of_ne_zero
        (den_add_ne_zero Fact.out (den_add_ne_zero Fact.out hd3 (by simp)) hd1) hd2,
      cast_add_of_ne_zero (den_add_ne_zero Fact.out hd3 (by simp)) hd1,
      cast_add_of_ne_zero hd3 (by simp), cast_intCast] at hc
  · have hℓmul : ℓ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
      rw [hℓdef]; exact slope_mul_add_eq hne h₁ h₂
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rwa [cast_mul_of_ne_zero hℓden (den_add_ne_zero Fact.out hdy1 hdy2),
      cast_add_of_ne_zero hdy1 hdy2, (cast_secant_num hd1 hd2).2] at hc

end

/-- If the doubled `x`-coordinate `addX x₁ x₂ (slope …)` has nonzero denominator mod `p`, then so
does the slope. -/
theorem slope_den_of_addX_den (hp : p.Prime)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have he : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₂ + x₁ + x₂ := by grind
  have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [he]
    exact den_add_ne_zero hp (den_add_ne_zero hp (den_add_ne_zero hp hd3 (by simp)) hd1) hd2
  rw [den_pow, Nat.cast_pow] at hℓ2
  exact fun h ↦ hℓ2 (by grind)

/-- The doubled `x`-coordinate `addX x₁ x₂ ℓ` survives reduction when the slope, `x₁` and `x₂`
all do: `addX = ℓ² - a₂ - x₁ - x₂` has nonzero denominator mod `p`. -/
theorem addX_den_ne (hp : p.Prime) {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [haddX]
  exact den_sub_ne_zero hp (den_sub_ne_zero hp (den_sub_ne_zero hp
    (den_pow_ne_zero hp hℓden 2) (by simp)) hd1) hd2

section
variable [Fact p.Prime]

/-! ### The reduced addition formulas -/

/-- In the genuine-tangent case the reduced secant slope equals the reduced tangent slope `ℓ`:
`slope x₁ x₁ y₁ y₁ = ℓ`, from the reduced tangent identity `htan`. -/
theorem reduced_slope_eq {ℓ : ZMod p} {x₁ y₁ : ZMod p}
    (hYneg : y₁ ≠ (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁)
    (h2Yne : y₁ + y₁ ≠ 0)
    (htan : ℓ * (y₁ + y₁) = x₁ ^ 2 + x₁ * x₁ + x₁ ^ 2 + a₂ * (x₁ + x₁) + a₄) :
    (curveZMod a₂ a₄ a₆ p).toAffine.slope x₁ x₁ y₁ y₁ = ℓ := by
  refine mul_right_cancel₀ h2Yne ?_
  rw [Affine.slope_of_Y_ne rfl hYneg]
  simp only [map_curveℤ_zmod, Affine.negY, zero_mul, sub_zero, sub_neg_eq_add]
  rw [div_mul_cancel₀ _ h2Yne]
  grind

/-- The reduced-curve `addX` at a doubled point unfolds to `ℓ² - a₂ - x - x`. -/
@[grind =]
theorem reduced_addX_eq {x ℓ : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.addX x x ℓ = ℓ ^ 2 - a₂ - x - x := by
  simp only [Affine.addX, map_curveℤ_zmod]; grind

/-- The reduced-curve `addY` at a doubled point unfolds to `-(ℓ·(addX - x) + y)`. -/
@[grind =]
theorem reduced_addY_eq {x y ℓ : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.addY x x y ℓ
      = -(ℓ * ((curveZMod a₂ a₄ a₆ p).toAffine.addX x x ℓ - x) + y) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY, map_curveℤ_zmod]; grind

/-- When the slope, `x`-coordinates and `y`-coordinate have nonzero denominators mod `p`, the cast
of the rational `addY` equals `-(ℓ·(addX - x₁) + y₁)` over `ZMod p`. -/
theorem addY_cast_eq {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hdy1 : (y₁.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0) :
    ((curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
      = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
  have haddY : (curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
    simp only [Affine.addY, Affine.negY, Affine.negAddY, curve]; grind
  rw [haddY, cast_neg,
    cast_add_of_ne_zero (den_mul_ne_zero Fact.out hℓden (den_sub_ne_zero Fact.out hd3 hd1)) hdy1,
    cast_mul_of_ne_zero hℓden (den_sub_ne_zero Fact.out hd3 hd1), cast_sub_of_ne_zero hd3 hd1]

end
end

/-! ## The kernel of reduction is closed under the group law -/

section

/-! ### Integer data attached to a kernel point -/

/-- `(q.num : ℚ) = q * wᵏ` when `q.den = wᵏ`, clearing the denominator of a rational. -/
theorem cast_num_eq {q : ℚ} {w k : ℕ} (hd : q.den = w ^ k) : (q.num : ℚ) = q * w ^ k := by
  rw [(div_eq_iff (mod_cast q.den_ne_zero)).mp (Rat.num_div_den q), hd]; grind

/-- The numerator of a rational with square denominator `w²` is coprime to any `p ∣ w`. -/
theorem not_dvd_num (hp : p.Prime) {q : ℚ} {w : ℤ} (hd : (q.den : ℤ) = w ^ 2) (hpw : (p : ℤ) ∣ w) :
    ¬ (p : ℤ) ∣ q.num := by
  intro hdvd
  have hcop : IsCoprime q.num (w ^ 2) := by
    rw [← hd, Int.isCoprime_iff_nat_coprime]; simpa using q.reduced
  exact absurd (Int.isUnit_iff.mp
    (hcop.isUnit_of_dvd' hdvd (hpw.trans (dvd_pow_self w two_ne_zero))))
    (by have := hp.two_le; lia)

variable {x y : ℚ}

/-- Coordinate data for a kernel point. If `(x, y)` satisfies the curve equation and reduces to
the origin (`p ∣ x.den`), it has integer coordinates `x = x.num/w²`, `y = y.num/w³` over a common
`w` with `p ∣ w`, `w ≠ 0` and `p`-unit numerator `x.num`. -/
theorem kernel_point_data (hp : p.Prime)
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hd : (x.den : ZMod p) = 0) :
    ∃ w : ℤ, (x.num : ℚ) = x * w ^ 2 ∧ (y.num : ℚ) = y * w ^ 3
      ∧ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) ∣ x.num ∧ w ≠ 0 := by
  obtain ⟨w, hxd, hyd⟩ := den_isSquare h
  have hpw : (p : ℤ) ∣ (w : ℤ) :=
    mod_cast hp.dvd_of_dvd_pow (hxd ▸ (ZMod.natCast_eq_zero_iff _ p).mp hd)
  have hwne : w ≠ 0 := by grind [Rat.den_ne_zero]
  exact ⟨w, cast_num_eq hxd, cast_num_eq hyd, hpw, not_dvd_num hp (by grind) hpw, by positivity⟩

/-- For a point `(A/E², B/E³)` on `y² = x³ + a₂x² + a₄x + a₆`, the integer relation
`B² = A³ + a₂A²E² + a₄AE⁴ + a₆E⁶`. -/
theorem int_curve_relation {A B E : ℤ}
    (hcv : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hA : (A : ℚ) = x * E ^ 2) (hB : (B : ℚ) = y * E ^ 3) :
    B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 := by
  have hq : (B : ℚ) ^ 2 = (A : ℚ) ^ 3 + a₂ * (A : ℚ) ^ 2 * (E : ℚ) ^ 2
      + a₄ * (A : ℚ) * (E : ℚ) ^ 4 + a₆ * (E : ℚ) ^ 6 := by grind
  exact mod_cast hq

/-! ### The certificate scalars -/

section
variable {x₁ y₁ x₂ y₂ : ℚ} {A B C D E G : ℤ}

/-- The scalar `W = -A²C² + a₄ACE²G² + a₆E²G²(AG² + CE²)` is a `p`-unit when `p ∣ E` and
`A`, `C` are `p`-units. -/
theorem not_dvd_W_cert (hpZ : Prime (p : ℤ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C) (hpE : (p : ℤ) ∣ E) :
    ¬ (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2)) := by
  intro hdvd
  have hrest : (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2) := by
    have heq : -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
          + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2
        = E ^ 2 * G ^ 2 * (a₄ * A * C + a₆ * (A * G ^ 2 + C * E ^ 2)) := by grind
    rw [heq]
    exact ((hpE.trans (dvd_pow_self E two_ne_zero)).mul_right (G ^ 2)).mul_right _
  have hAC : (p : ℤ) ∣ A ^ 2 * C ^ 2 := by simpa using dvd_sub hrest hdvd
  grind [Prime.dvd_of_dvd_pow, Prime.dvd_mul]

/-- The scalar `K = A·G² - C·E²` is nonzero when `x₁ ≠ x₂`, given `A = x₁E²`, `C = x₂G²`
and `E`, `G` nonzero. -/
theorem K_ne_zero (hne : x₁ ≠ x₂)
    (hA : (A : ℚ) = x₁ * E ^ 2) (hC : (C : ℚ) = x₂ * G ^ 2)
    (hEQ : (E : ℚ) ≠ 0) (hGQ : (G : ℚ) ≠ 0) :
    A * G ^ 2 - C * E ^ 2 ≠ 0 := fun h ↦ hne <| by
  have h0 : ((A * G ^ 2 - C * E ^ 2 : ℤ) : ℚ) = 0 := by rw [h]; simp
  push_cast at h0
  grind [mul_right_cancel₀, pow_ne_zero]

/-- The single-fraction identity `x₃·(A·C·K²) = N² - a₆E²G²K²` for the doubled `x`-coordinate,
with `K = AG² - CE²` and `N = ADE - BCG`. -/
theorem addX_single_fraction {ℓ x₃ : ℚ}
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂) (haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (hcv1 : y₁ ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (hcv2 : y₂ ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hA : (A : ℚ) = x₁ * E ^ 2) (hB : (B : ℚ) = y₁ * E ^ 3)
    (hC : (C : ℚ) = x₂ * G ^ 2) (hD : (D : ℚ) = y₂ * G ^ 3) :
    x₃ * ((A * C * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ)
      = (((A * D * E - B * C * G) ^ 2
        - a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ) := by
  rw [haddX]
  push_cast
  rw [hA, hB, hC, hD]
  linear_combination
    ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₁ * x₂ * (ℓ * x₁ - ℓ * x₂ + y₁ - y₂))) * hℓ
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₂ * (x₁ - x₂))) * hcv1
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (-x₁ * (x₁ - x₂))) * hcv2

/-! ### The valuation argument -/

/-- With `v_p(N) < v_p(K)`, the integer `N² - M·K²` is nonzero and has `v_p = 2·v_p(N)`. -/
theorem padicValRat_num_cert (hp : p.Prime) {N K M : ℤ}
    (hcrux : padicValInt p N < padicValInt p K) (hN0 : N ≠ 0) (hK0 : K ≠ 0) :
    padicValRat p (N ^ 2 - M * K ^ 2 : ℤ) = 2 * padicValInt p N ∧ N ^ 2 - M * K ^ 2 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain rfl | hM := eq_or_ne M 0
  · simp [hN0]
  have : padicValRat p (N ^ 2 : ℤ) < padicValRat p (-(M * K ^ 2 : ℤ)) := by
    simp [padicValRat.mul, hM, hK0]; grind
  have hne : N ^ 2 ≠ M * K ^ 2 := by contrapose! this; simp [this]
  have hne' : (↑(N ^ 2 : ℤ) + -↑(M * K ^ 2) : ℚ) ≠ 0 := by qify at hne; grind
  refine ⟨?_, by grind only⟩
  rw [Int.cast_sub, sub_eq_add_neg, padicValRat.add_eq_of_lt hne' _ _ this]
  all_goals simp [*]

/-- For the single-fraction `x₃ = (N² - M·K²)/(A·C·K²)` with `p`-unit `A`, `C` and
`v_p(N) < v_p(K)`, the `p`-adic valuation of `x₃` is negative, so `p ∣ x₃.den`. -/
theorem den_zero_of_cert (hp : p.Prime) {x₃ : ℚ} {K N M : ℤ}
    (hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hcrux : padicValInt p N < padicValInt p K)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (hK0 : K ≠ 0) (hN0 : N ≠ 0) :
    (x₃.den : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNumvalQ, hNum0⟩ := padicValRat_num_cert hp (M := M) hcrux hN0 hK0
  have hDenval : padicValInt p (A * C * K ^ 2) = 2 * padicValInt p K := by
    rw [padicValInt.mul (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0), padicValInt.mul hA0 hC0,
      padicValInt.eq_zero_of_not_dvd hpA, padicValInt.eq_zero_of_not_dvd hpC,
      pow_two, padicValInt.mul hK0 hK0]
    grind
  have hDen3Q : ((A * C * K ^ 2 : ℤ) : ℚ) ≠ 0 := by
    exact mod_cast (mul_ne_zero (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0))
  have hx3div : x₃ = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ) / ((A * C * K ^ 2 : ℤ) : ℚ) := by
    rw [eq_div_iff hDen3Q]; exact hMain
  have hx3neg : padicValRat p x₃ < 0 := by
    rw [hx3div, padicValRat.div (mod_cast hNum0) hDen3Q, hNumvalQ, padicValRat.of_int, hDenval]
    grind
  have hden0 : padicValNat p x₃.den ≠ 0 := by rw [padicValRat_def] at hx3neg; lia
  exact (ZMod.natCast_eq_zero_iff _ p).mpr ((dvd_iff_padicValNat_ne_zero x₃.den_ne_zero).mpr hden0)

/-- The valuation inequality `v_p(N) < v_p(K)`, with `N ≠ 0` and `K ≠ 0`, for `K = AG² - CE²`,
`N = ADE - BCG` under `p ∣ E`, `p ∣ G` and `p`-unit `A`, `C`. -/
theorem crux_of_int_relations (hpZ : Prime (p : ℤ))
    (hne : x₁ ≠ x₂) (hA : (A : ℚ) = x₁ * E ^ 2) (hC : (C : ℚ) = x₂ * G ^ 2)
    (hEne : (E : ℚ) ≠ 0) (hGne : (G : ℚ) ≠ 0) (hpE : (p : ℤ) ∣ E) (hpG : (p : ℤ) ∣ G)
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6)
    (hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6) :
    padicValInt p (A * D * E - B * C * G) < padicValInt p (A * G ^ 2 - C * E ^ 2)
      ∧ A * D * E - B * C * G ≠ 0 ∧ A * G ^ 2 - C * E ^ 2 ≠ 0 := by
  have : Fact p.Prime := ⟨Nat.prime_iff_prime_int.mpr hpZ⟩
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  set W : ℤ := -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
    + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) with hWdef
  have hI2 : N * (A * D * E + B * C * G) = K * W := by grind
  have hpS : (p : ℤ) ∣ (A * D * E + B * C * G) :=
    dvd_add (hpE.mul_left (A * D)) (hpG.mul_left (B * C))
  have hpW : ¬ (p : ℤ) ∣ W := hWdef ▸ not_dvd_W_cert hpZ hpA hpC hpE
  have hW0 : W ≠ 0 := fun h ↦ hpW (h ▸ dvd_zero _)
  have hK0 : K ≠ 0 := hKdef ▸ K_ne_zero hne hA hC hEne hGne
  have hprodne : N * (A * D * E + B * C * G) ≠ 0 := hI2 ▸ mul_ne_zero hK0 hW0
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hprodne
  refine ⟨?_, hN0, hK0⟩
  replace hI2 := congr(padicValInt p $hI2)
  rw [padicValInt.mul hN0 (by lia), padicValInt.mul hK0 hW0,
    padicValInt.eq_zero_of_not_dvd hpW] at hI2
  have : 1 ≤ padicValInt p (A * D * E + B * C * G) := by
    apply one_le_padicValNat_of_dvd (by grind)
    rwa [← Int.ofNat_dvd_left]
  grind

end

/-! ### Closure of the kernel -/

/-- If two affine points both reduce to the origin mod `p` (`p ∣ x₁.den`, `p ∣ x₂.den`) but are
distinct over `ℚ`, the `x`-coordinate `x₃ = addX x₁ x₂ (slope …)` of their sum satisfies
`p ∣ x₃.den`, so the sum reduces to the origin as well. -/
theorem den_addX_both_kernel (hp : p.Prime) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hne : x₁ ≠ x₂) (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by grind [Affine.slope_of_X_ne]
  have haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by rw [hx3def, curve_addX]
  have hcv1 := equation_curve h₁
  have hcv2 := equation_curve h₂
  obtain ⟨E, hA, hB, hpE, hpA, hEne⟩ := kernel_point_data hp h₁ hd1
  obtain ⟨G, hC, hD, hpG, hpC, hGne⟩ := kernel_point_data hp h₂ hd2
  set A : ℤ := x₁.num
  set B : ℤ := y₁.num
  set C : ℤ := x₂.num
  set D : ℤ := y₂.num
  -- integer curve relations
  have hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 :=
    int_curve_relation hcv1 hA hB
  have hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6 :=
    int_curve_relation hcv2 hC hD
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  -- the single-fraction identity for the final valuation certificate
  have hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) := by
    rw [hKdef, hNdef]; exact addX_single_fraction hℓ haddX hcv1 hcv2 hA hB hC hD
  -- the crux inequality `v_p(N) < v_p(K)`, with nonzeroness, from the integer curve relations
  obtain ⟨hcrux, hN0, hK0⟩ := crux_of_int_relations hpZ hne hA hC
    (mod_cast hEne) (mod_cast hGne) hpE hpG hpA hpC hCR1 hCR2
  exact den_zero_of_cert hp (M := a₆ * E ^ 2 * G ^ 2) hMain hpA hpC hcrux
    (fun h ↦ hpA (h ▸ dvd_zero _)) (fun h ↦ hpC (h ▸ dvd_zero _)) hK0 hN0
end

/-! ## Additivity of the reduction map -/

section
open Projective

variable [Fact p.Prime]

/-- Over `ℚ`, the affine point underlying the integer representative `trep x y w` is `(x, y)`. -/
theorem toAffine_g_trep {x y : ℚ} {w : ℕ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ trep x y w)
      = .some x y h := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rw [trep_map_ℚ hden hden',
    Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (by positivity)),
    Point.toAffine_some ((nonsingular_some x y).mpr h)]

/-- An integer projective representative whose rational affine point is a `some` is nonsingular
over `ℚ` (the affine point of a singular representative is the origin). -/
theorem nonsingular_of_toAffine_some {U : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hU : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U) = .some X Y hR) :
    (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) := by
  grind [Point.toAffine_of_singular, Affine.Point.some_ne_zero]

/-- If two integer projective representatives have the same (rational) affine point, then they are
proportional over `ℤ`, with the cross scalars given by each other's `Z`-coordinate. -/
theorem int_smul_eq_of_toAffine_eq {S T : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hS : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ S) = .some X Y hR)
    (hT : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T) = .some X Y hR) :
    T 2 • S = S 2 • T := by
  have key : ∀ U : Fin 3 → ℤ,
      Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U)
        = .some X Y hR → (U 0 : ℚ) = X * U 2 ∧ (U 1 : ℚ) = Y * U 2 := by
    intro U hU
    have hg : ∀ i, (Int.castRingHom ℚ ∘ U) i = (U i : ℚ) := fun i ↦ by simp [Function.comp_apply]
    have hUz : (Int.castRingHom ℚ ∘ U) 2 ≠ 0 := by
      grind [Point.toAffine_of_Z_eq_zero, Affine.Point.some_ne_zero]
    have hns : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) :=
      nonsingular_of_toAffine_some hU
    rw [Point.toAffine_of_Z_ne_zero hns hUz, Affine.Point.some.injEq] at hU
    rw [hg] at hUz
    exact ⟨(div_eq_iff hUz).mp (hg 0 ▸ hU.1), (div_eq_iff hUz).mp (hg 1 ▸ hU.2)⟩
  obtain ⟨hS0, hS1⟩ := key S hS
  obtain ⟨hT0, hT1⟩ := key T hT
  funext i
  fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
  · have : ((T 2 * S 0 : ℤ) : ℚ) = ((S 2 * T 0 : ℤ) : ℚ) := by grind
    exact mod_cast this
  · have : ((T 2 * S 1 : ℤ) : ℚ) = ((S 2 * T 1 : ℤ) : ℚ) := by grind
    exact mod_cast this
  · exact mul_comm _ _

/-- Reduction is well-defined on classes: any integer projective representative `T` whose
rational affine point is `R` reduces mod `p` to a representative equivalent to `repr R`. -/
theorem repr_equiv_of_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (R : (curve a₂ a₄ a₆).toAffine.Point) {T : Fin 3 → ℤ}
    (hnsp : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ T))
    (hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ T))
    (hTℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T) = R) :
    repr p R ≈ Int.castRingHom (ZMod p) ∘ T := by
  cases R with
  | zero =>
    have hTz : (Int.castRingHom ℚ ∘ T) 2 = 0 := by
      grind [Point.toAffine_of_Z_ne_zero, Affine.Point.some_ne_zero]
    have hTz' : T 2 = 0 := by simpa [Function.comp_apply] using hTz
    have hfTz : (Int.castRingHom (ZMod p) ∘ T) 2 = 0 := by simp [Function.comp_apply, hTz']
    rw [repr_zero]
    exact Setoid.symm (equiv_zero_of_Z_eq_zero hnsp hfTz)
  | some X Y hR =>
    obtain ⟨w₃, hd3, hd3'⟩ := den_isSquare hR.1
    have hrepr : repr p (.some X Y hR) = Int.castRingHom (ZMod p) ∘ trep X Y w₃ :=
      repr_some hR hd3 hd3'
    have hStℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective
        (Int.castRingHom ℚ ∘ trep X Y w₃) = .some X Y hR :=
      toAffine_g_trep hR hd3 hd3'
    have hid : T 2 • trep X Y w₃ = trep X Y w₃ 2 • T := int_smul_eq_of_toAffine_eq hStℚ hTℚ
    have hprop : (Int.castRingHom (ZMod p) ∘ T) 2 •
          (Int.castRingHom (ZMod p) ∘ trep X Y w₃)
        = (Int.castRingHom (ZMod p) ∘ trep X Y w₃) 2 • (Int.castRingHom (ZMod p) ∘ T) := by
      have h := congrArg (fun Q : Fin 3 → ℤ ↦ Int.castRingHom (ZMod p) ∘ Q) hid
      simpa only [comp_smul, Function.comp_apply] using h
    have hns_repr := repr_nonsingular hΔ (.some X Y hR)
    rw [hrepr] at hns_repr ⊢
    exact equiv_of_proportional hns_repr hnsp hprop

/-- Common closing step for the doubling and secant cases of additivity: an integer
representative `V` whose reduction is the reduced sum (`hadd`) and whose rational value is the
rational sum of two nonsingular representatives `A`, `B` (`hgadd`) is equivalent mod `p` to `repr`
of the affine sum `toAffine A + toAffine B`. -/
theorem sum_repr_equiv (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {V : Fin 3 → ℤ}
    {A B : Fin 3 → ℚ} (P Q : (curve a₂ a₄ a₆).toAffine.Point)
    (hnsA : (curve a₂ a₄ a₆).toProjective.Nonsingular A)
    (hnsB : (curve a₂ a₄ a₆).toProjective.Nonsingular B)
    (hgadd : Int.castRingHom ℚ ∘ V = (curve a₂ a₄ a₆).toProjective.add A B)
    (haffA : Point.toAffine (curve a₂ a₄ a₆).toProjective A = P)
    (haffB : Point.toAffine (curve a₂ a₄ a₆).toProjective B = Q)
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
      (repr p P) (repr p Q) = Int.castRingHom (ZMod p) ∘ V) :
    repr p (P + Q) ≈ Int.castRingHom (ZMod p) ∘ V := by
  have hnsp : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ V) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)
  have hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ V) := by
    rw [hgadd]; exact nonsingular_add hnsA hnsB
  have hTℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ V)
      = P + Q := by rw [hgadd, Point.toAffine_add hnsA hnsB, haffA, haffB]
  exact repr_equiv_of_toAffine hΔ _ hnsp hnsq hTℚ

/-! ### Case analysis for the group law -/

variable {x₁ y₁ x₂ y₂ : ℚ}

/-- Distinct points sharing an `x`-coordinate are mutually negative: if `x₁ = x₂` but
`(x₁, y₁) ≠ (x₂, y₂)`, then `y₁ = negY x₂ y₂` (so `P + Q = O`). -/
theorem y_eq_negY_of_X_eq
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hx12 : x₁ = x₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
  have := Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12
  grind [Affine.Point.some.injEq]

/-- Additivity of `redP` in the tangent-mod-`p` `2`-torsion sub-case: the shared reduced point
satisfies `Ȳ₁ = -Ȳ₁`, and both `redP (P + Q)` and `P̄ + P̄` are the origin. -/
theorem redP_add_tangent_two_torsion (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = x₂) (hYbar : (y₁ : ZMod p) = y₂)
    (hYneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  rw [redP_of_den_ne hΔ h₁ hd1, Affine.Point.add_of_Y_eq rfl hYneg, Affine.Point.add_of_X_ne hne]
  apply redP_of_den_zero (Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left))
  by_contra hd3_s
  obtain ⟨-, htan⟩ :=
    reduced_tangent_eqs hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2
      (slope_den_of_addX_den Fact.out hd1 hd2 hd3_s) hd3_s
  have hYeq : (y₁ : ZMod p) = -y₁ := hYneg.trans reduced_negY
  have hY0 : (y₁ : ZMod p) + y₂ = 0 := by grind
  rw [hY0, mul_zero] at htan
  have hfd : 3 * (x₁ : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x₁ : ZMod p) + (a₄ : ZMod p) = 0 := by
    grind
  have hns : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p) :=
    red_nonsingular_affine hΔ h₁ hd1
  rw [Affine.nonsingular_iff, map_curveℤ_zmod] at hns
  simp only [zero_mul, sub_zero] at hns
  exact hns.2.elim (fun hfd_ne ↦ (Ne.symm hfd_ne) hfd) (fun hyne2 ↦ hyne2 hYeq)

/-- Tangent-mod-`p` additivity, genuine-tangent sub-case (`Ȳ₁ + Ȳ₂ ≠ 0`): the reduced sum
`redP (P + Q)` is the tangent doubling of the common reduced point `P̄`. Both reduced `x`- and
`y`-coordinates are matched against the doubling formulas via the reduced tangent identities. -/
theorem redP_add_tangent_generic (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = x₂) (hYbar : (y₁ : ZMod p) = y₂)
    (hYneg : ¬ (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  have hslX : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
    Affine.slope_of_X_ne hne
  set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂) with hℓdef
  have hy2 : (y₁ : ZMod p) + y₂ ≠ 0 := by grind
  have hℓden_s : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 :=
    reduced_slope_den hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hy2
  have hℓden : (ℓ.den : ZMod p) ≠ 0 := by rwa [← hslX]
  have hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 :=
    addX_den_ne Fact.out hℓden hd1 hd2 curve_addX
  have hd3_s : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0 := by rwa [hslX]
  obtain ⟨hS2, htan⟩ := reduced_tangent_eqs hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
  rw [hslX] at hS2 htan
  have h2Yne : (y₁ : ZMod p) + y₁ ≠ 0 := by grind
  rw [← hXbar, ← hYbar] at htan
  have hℓd := reduced_slope_eq hYneg h2Yne htan
  have hy3cast := addY_cast_eq hℓden hd1 hdy1 hd3
  have hns3 := Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left)
  grind [Affine.Point.add_of_X_ne, redP_of_den_ne, Affine.Point.add_of_Y_ne]

/-- Additivity when both summands reduce to the origin (`p ∣ x₁.den`, `p ∣ x₂.den`): the sum also
reduces to the origin. Uses `den_addX_both_kernel`. -/
theorem redP_add_kernel
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  obtain rfl | hx12 := eq_or_ne x₁ x₂
  · rw [Affine.Point.add_of_Y_eq rfl (y_eq_negY_of_X_eq h₁ h₂ rfl hPQ), redP_zero]
  · rw [Affine.Point.add_of_X_ne hx12]
    exact redP_of_den_zero _ (den_addX_both_kernel Fact.out h₁.1 h₂.1 hx12 hd1 hd2)

/-- Additivity when the reduced points coincide and `Q = -P` over `ℚ` (`x₁ = x₂`): then `P + Q = 0`
and the common reduced point is `2`-torsion, so `redP (P + Q) = 0 = P̄ + P̄`. -/
theorem redP_add_neg (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hx12 : x₁ = x₂) (hYbar : (y₁ : ZMod p) = y₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  have hy : y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := y_eq_negY_of_X_eq h₁ h₂ hx12 hPQ
  rw [Affine.Point.add_of_Y_eq hx12 hy, redP_zero, redP_of_den_ne hΔ h₁ hd1]
  have hyneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY
      (x₁ : ZMod p) (y₁ : ZMod p) := by
    have hcast : (y₁ : ZMod p) = -y₂ := by
      rw [hy, Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl, Rat.cast_neg]
    grind
  rw [Affine.Point.add_of_Y_eq rfl hyneg]

/-- Additivity of `redP` when two affine points `P`, `Q` reduce to the same point of `E/𝔽ₚ`
(`redP P = redP Q`) but are distinct over `ℚ`: the reduction of their rational sum equals the
sum of their reductions. -/
theorem redP_add_tangent (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hred : redP p (.some x₁ y₁ h₁) = redP p (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₂ y₂ h₂) := by
  by_cases hd1 : (x₁.den : ZMod p) = 0
  · -- `P → O`, hence (by `hred`) `Q → O` as well; the sum reduces to `O`.
    have hQ0 : redP p (.some x₂ y₂ h₂) = 0 := by rw [← hred]; exact redP_of_den_zero h₁ hd1
    have hd2 : (x₂.den : ZMod p) = 0 := by grind [redP_of_den_ne, Affine.Point.some_ne_zero]
    rw [redP_of_den_zero h₁ hd1, hQ0, add_zero]
    exact redP_add_kernel h₁ h₂ hPQ hd1 hd2
  · -- `P` has good reduction; then so does `Q`, and they share reduced coordinates.
    have hd2 : (x₂.den : ZMod p) ≠ 0 := by
      grind [redP_of_den_ne, redP_of_den_zero, Affine.Point.some_ne_zero]
    rw [redP_of_den_ne hΔ h₁ hd1, redP_of_den_ne hΔ h₂ hd2, Affine.Point.some.injEq] at hred
    obtain ⟨hXbar, hYbar⟩ := hred
    -- Rewrite `red Q` to `red P` throughout: the two reduced points coincide.
    have hQeqP : redP p (.some x₂ y₂ h₂) = redP p (.some x₁ y₁ h₁) := by
      rw [redP_of_den_ne hΔ h₁ hd1, redP_of_den_ne hΔ h₂ hd2, Affine.Point.some.injEq]
      exact ⟨hXbar.symm, hYbar.symm⟩
    rw [hQeqP]
    obtain rfl | hx12 := eq_or_ne x₁ x₂
    · -- `Q = -P`, so `P + Q = 0`, and the common reduced point is `2`-torsion.
      exact redP_add_neg hΔ h₁ h₂ hPQ hd1 rfl hYbar
    · -- `x₁ ≠ x₂` over `ℚ` but the reduced points coincide: the tangent-mod-`p` case, split on
      -- whether the common reduced point is `2`-torsion.
      have hp : p.Prime := Fact.out
      have hdy1 : (y₁.den : ZMod p) ≠ 0 := by grind [ydenom_eq_zero_iff, h₁.1]
      have hdy2 : (y₂.den : ZMod p) ≠ 0 := by grind [ydenom_eq_zero_iff, h₂.1]
      by_cases hYneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY
          (x₁ : ZMod p) (y₁ : ZMod p)
      · exact redP_add_tangent_two_torsion hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2 hXbar hYbar hYneg
      · exact redP_add_tangent_generic hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2 hXbar hYbar hYneg

/-! ### The homomorphism -/

/-- Additivity of `redP` on `some + some` when the two reduced representatives are proportional
mod `p` and the points are equal over `ℚ`: the reduced sum is an honest doubling. -/
theorem redP_map_add_double (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ : ℕ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (hden1 : x₁.den = w₁ ^ 2) (hden1' : y₁.den = w₁ ^ 3)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁))
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₁ y₁ h₁))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁)) :
    repr p (.some x₁ y₁ h₁ + .some x₁ y₁ h₁)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁) := by
  have hgadd : Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁)
      = (curve a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁) := by
    rw [add_self, ← map_curveℤ_ℚ]
    exact (map_dblXYZ (Int.castRingHom ℚ) _).symm
  exact sum_repr_equiv hΔ _ _ hns1 hns1 hgadd
    (toAffine_g_trep h₁ hden1 hden1')
    (toAffine_g_trep h₁ hden1 hden1') hadd

/-- Additivity of `redP` on `some + some` in the secant case (`¬ repr P ≈ repr Q` mod `p`): the
reduced sum is a secant, and the two representatives are also inequivalent over `ℚ`. -/
theorem redP_map_add_secant (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ w₂ : ℕ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hden1 : x₁.den = w₁ ^ 2) (hden1' : y₁.den = w₁ ^ 3)
    (hden2 : x₂.den = w₂ ^ 2) (hden2' : y₂.den = w₂ ^ 3)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁))
    (hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂))
    (heq : ¬ repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂)) :
    repr p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
          (trep x₂ y₂ w₂) := by
  have hℚne : ¬ Int.castRingHom ℚ ∘ trep x₁ y₁ w₁ ≈ Int.castRingHom ℚ ∘ trep x₂ y₂ w₂ := by
    intro hℚeq
    apply heq
    have hpt : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂ := by
      rw [← toAffine_g_trep h₁ hden1 hden1', ← toAffine_g_trep h₂ hden2 hden2']
      exact Point.toAffine_of_equiv hℚeq
    exact hpt ▸ Setoid.refl (repr p (.some x₁ y₁ h₁))
  have hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
          (trep x₂ y₂ w₂) := by
    rw [add_of_not_equiv heq, repr_some h₁ hden1 hden1', repr_some h₂ hden2 hden2']
    exact map_addXYZ (Int.castRingHom (ZMod p)) _ _
  have hgaddXYZ : (curve a₂ a₄ a₆).toProjective.addXYZ (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
        (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂)
      = Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
          (trep x₂ y₂ w₂) := by rw [← map_curveℤ_ℚ]; exact map_addXYZ (Int.castRingHom ℚ) _ _
  have hgadd : Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
        (trep x₂ y₂ w₂)
      = (curve a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂) := by
    rw [← hgaddXYZ]; exact (add_of_not_equiv hℚne).symm
  exact sum_repr_equiv hΔ _ _ hns1 hns2 hgadd
    (toAffine_g_trep h₁ hden1 hden1') (toAffine_g_trep h₂ hden2 hden2') hadd

/-- Additivity of `redP` on `some + some` in the tangent-mod-`p` case: the reduced
representatives are proportional but the points differ over `ℚ`. The projective-class goal is
reduced to the affine additivity supplied by `redP_add_tangent`. -/
theorem redP_map_add_tangent_case (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ : ℕ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (heq : repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁)) :
    repr p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁) := by
  have hred : redP p (.some x₁ y₁ h₁) = redP p (.some x₂ y₂ h₂) := by
    rw [redP_eq_toAffine, redP_eq_toAffine]; exact Point.toAffine_of_equiv heq
  have hnspV : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁)) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)
  refine equiv_of_toAffine_eq (repr_nonsingular hΔ _) hnspV ?_
  rw [← redP_eq_toAffine, ← hadd,
    Point.toAffine_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _),
    ← redP_eq_toAffine, ← redP_eq_toAffine]
  exact redP_add_tangent hΔ h₁ h₂ hred hPQ

/-- Additivity of the reduction map on two `some` points, reduced to a projective-class
equivalence and dispatched to the doubling, tangent-mod-`p` and secant sub-cases. -/
theorem redP_map_add_some (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₂ y₂ h₂) := by
  obtain ⟨w₁, hden1, hden1'⟩ := den_isSquare h₁.1
  obtain ⟨w₂, hden2, hden2'⟩ := den_isSquare h₂.1
  have hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁) :=
    nonsingular_of_toAffine_some (toAffine_g_trep h₁ hden1 hden1')
  have hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂) :=
    nonsingular_of_toAffine_some (toAffine_g_trep h₂ hden2 hden2')
  rw [redP_eq_toAffine, redP_eq_toAffine (.some x₁ y₁ h₁),
    redP_eq_toAffine (.some x₂ y₂ h₂),
    ← Point.toAffine_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)]
  refine Point.toAffine_of_equiv ?_
  by_cases heq : repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂)
  · -- `repr P ≈ repr Q` mod `p`: the reduced sum is a doubling of `repr P`.
    have hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
          (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
        = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁) := by
      rw [add_of_equiv heq, repr_some h₁ hden1 hden1']
      exact map_dblXYZ (Int.castRingHom (ZMod p)) _
    rw [hadd]
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂
    · rw [← hPQ] at hadd ⊢; exact redP_map_add_double hΔ h₁ hden1 hden1' hns1 hadd
    · exact redP_map_add_tangent_case hΔ h₁ h₂ heq hPQ hadd
  · rw [add_of_not_equiv heq, repr_some h₁ hden1 hden1',
      repr_some h₂ hden2 hden2', map_addXYZ (Int.castRingHom (ZMod p))]
    exact redP_map_add_secant hΔ h₁ h₂ hden1 hden1' hden2 hden2' hns1 hns2 heq

/-- Additivity of the reduction map. -/
theorem redP_map_add (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    redP p (P + Q) = redP p P + redP p Q := by
  cases P with
  | zero =>
      change redP p (0 + Q) = redP p 0 + redP p Q
      rw [zero_add, redP_zero, zero_add]
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero =>
      change redP p (Affine.Point.some x₁ y₁ h₁ + 0)
        = redP p (.some x₁ y₁ h₁) + redP p 0
      rw [add_zero, redP_zero, add_zero]
  | some x₂ y₂ h₂ => exact redP_map_add_some hΔ h₁ h₂

/-- The reduction map bundled as an additive homomorphism
`(curve …).toAffine.Point →+ ((curveℤ …).map (Int.castRingHom (ZMod p))).toAffine.Point`. -/
@[expose, simps]
public noncomputable def redHom (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+ (curveZMod a₂ a₄ a₆ p).toAffine.Point where
  toFun := redP p
  map_zero' := redP_zero
  map_add' := by exact redP_map_add hΔ
end

end ECCompute
