/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Reduction.RedP
import ECCompute.ForMathlib.PadicValInt

/-!
# The kernel of reduction is closed under the group law

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` and a prime `p` of good reduction, two affine
points that reduce to the origin mod `p` and are distinct over `ℚ` have a secant sum whose
`x`-coordinate again has a denominator divisible by `p`.

## Main declarations

* `ECCompute.den_addX_both_kernel`: the `x`-coordinate of the secant sum has a `p`-divisible
  denominator.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} [Fact p.Prime]

/-! ### Integer data attached to a kernel point -/

/-- `(q.num : ℚ) = q * wᵏ` when `q.den = wᵏ`, clearing the denominator of a rational. -/
theorem cast_num_eq {q : ℚ} {w k : ℕ} (hd : q.den = w ^ k) : (q.num : ℚ) = q * (w : ℚ) ^ k := by
  rw [(div_eq_iff (mod_cast q.den_ne_zero)).mp (Rat.num_div_den q), hd]; grind

/-- The numerator of a rational with square denominator `w²` is coprime to any `p ∣ w`. -/
theorem not_dvd_num {q : ℚ} {w : ℤ} (hd : (q.den : ℤ) = w ^ 2) (hpw : (p : ℤ) ∣ w) :
    ¬ (p : ℤ) ∣ q.num := by
  intro hdvd
  have hcop : IsCoprime q.num (w ^ 2) := by
    rw [← hd, Int.isCoprime_iff_nat_coprime]; simpa using q.reduced
  exact absurd (Int.isUnit_iff.mp
    (hcop.isUnit_of_dvd' hdvd (hpw.trans (dvd_pow_self w two_ne_zero))))
    (by have := (Fact.out : p.Prime).two_le; lia)

variable {x y : ℚ}

/-- Coordinate data for a kernel point. If `(x, y)` satisfies the curve equation and reduces to
the origin (`p ∣ x.den`), it has integer coordinates `x = x.num/w²`, `y = y.num/w³` over a common
`w` with `p ∣ w`, `w ≠ 0` and `p`-unit numerator `x.num`. -/
theorem kernel_point_data
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hd : (x.den : ZMod p) = 0) :
    ∃ w : ℤ, (x.num : ℚ) = x * (w : ℚ) ^ 2 ∧ (y.num : ℚ) = y * (w : ℚ) ^ 3
      ∧ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) ∣ x.num ∧ w ≠ 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hxd, hyd⟩ := den_isSquare h
  have hpw : (p : ℤ) ∣ (w : ℤ) :=
    mod_cast hp.dvd_of_dvd_pow (hxd ▸ (ZMod.natCast_eq_zero_iff _ p).mp hd)
  have hwne : w ≠ 0 := by grind [Rat.den_ne_zero]
  exact ⟨w, cast_num_eq hxd, cast_num_eq hyd, hpw, not_dvd_num (by grind) hpw, by positivity⟩

/-- For a point `(A/E², B/E³)` on `y² = x³ + a₂x² + a₄x + a₆`, the integer relation
`B² = A³ + a₂A²E² + a₄AE⁴ + a₆E⁶`. -/
theorem int_curve_relation {A B E : ℤ}
    (hcv : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hA : (A : ℚ) = x * (E : ℚ) ^ 2) (hB : (B : ℚ) = y * (E : ℚ) ^ 3) :
    B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 := by
  have hq : (B : ℚ) ^ 2 = (A : ℚ) ^ 3 + a₂ * (A : ℚ) ^ 2 * (E : ℚ) ^ 2
      + a₄ * (A : ℚ) * (E : ℚ) ^ 4 + a₆ * (E : ℚ) ^ 6 := by grind
  exact mod_cast hq

/-! ### The certificate scalars -/

section
variable {x₁ y₁ x₂ y₂ : ℚ} {A B C D E G : ℤ}

omit [Fact p.Prime] in
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
    (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2)
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
    (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hB : (B : ℚ) = y₁ * (E : ℚ) ^ 3)
    (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2) (hD : (D : ℚ) = y₂ * (G : ℚ) ^ 3) :
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
theorem padicValRat_num_cert {N K M : ℤ} (hcrux : padicValInt p N < padicValInt p K)
    (hN0 : N ≠ 0) (hK0 : K ≠ 0) :
    padicValRat p ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ) = (2 * padicValInt p N : ℤ)
      ∧ (N ^ 2 - M * K ^ 2 : ℤ) ≠ 0 := by
  have hK2 : padicValInt p (K ^ 2) = 2 * padicValInt p K := by
    rw [pow_two, padicValInt.mul hK0 hK0]; grind
  have hNval2 : padicValInt p (N ^ 2) = 2 * padicValInt p N := by
    rw [pow_two, padicValInt.mul hN0 hN0]; grind
  have hqv : padicValRat p ((N ^ 2 : ℤ) : ℚ) = (2 * padicValInt p N : ℤ) := by
    rw [padicValRat.of_int, hNval2]; grind
  rcases eq_or_ne (M * K ^ 2 : ℤ) 0 with h0 | h0
  · rw [h0, sub_zero]; exact ⟨hqv, pow_ne_zero 2 hN0⟩
  · have hsplit : ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ)
        = ((N ^ 2 : ℤ) : ℚ) + (-((M * K ^ 2 : ℤ) : ℚ)) := by grind
    have hq0 : ((N ^ 2 : ℤ) : ℚ) ≠ 0 := mod_cast pow_ne_zero 2 hN0
    have hr0 : (-((M * K ^ 2 : ℤ) : ℚ)) ≠ 0 := by
      have : ((M * K ^ 2 : ℤ) : ℚ) ≠ 0 := mod_cast h0
      simpa using this
    have hlt : padicValRat p ((N ^ 2 : ℤ) : ℚ) < padicValRat p (-((M * K ^ 2 : ℤ) : ℚ)) := by
      rw [hqv, padicValRat.neg, padicValRat.of_int]
      have hle := padicValInt_mono (p := p) Fact.out (a := K ^ 2) (b := M * K ^ 2) ⟨M, by ring⟩ h0
      rw [hK2] at hle
      lia
    have hqrne : ((N ^ 2 : ℤ) : ℚ) + (-((M * K ^ 2 : ℤ) : ℚ)) ≠ 0 := fun he ↦ by
      have heq : ((N ^ 2 : ℤ) : ℚ) = ((M * K ^ 2 : ℤ) : ℚ) := by grind
      rw [heq, padicValRat.neg] at hlt
      exact lt_irrefl _ hlt
    refine ⟨by rw [hsplit, padicValRat.add_eq_of_lt hqrne hq0 hr0 hlt, hqv], ?_⟩
    intro he
    apply hqrne
    rw [← hsplit]
    exact mod_cast he

/-- For the single-fraction `x₃ = (N² - M·K²)/(A·C·K²)` with `p`-unit `A`, `C` and
`v_p(N) < v_p(K)`, the `p`-adic valuation of `x₃` is negative, so `p ∣ x₃.den`. -/
theorem den_zero_of_cert {x₃ : ℚ} {K N M : ℤ}
    (hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hcrux : padicValInt p N < padicValInt p K)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (hK0 : K ≠ 0) (hN0 : N ≠ 0) :
    (x₃.den : ZMod p) = 0 := by
  obtain ⟨hNumvalQ, hNum0⟩ := padicValRat_num_cert (M := M) hcrux hN0 hK0
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
    (hne : x₁ ≠ x₂) (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2)
    (hEne : (E : ℚ) ≠ 0) (hGne : (G : ℚ) ≠ 0) (hpE : (p : ℤ) ∣ E) (hpG : (p : ℤ) ∣ G)
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6)
    (hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6) :
    padicValInt p (A * D * E - B * C * G) < padicValInt p (A * G ^ 2 - C * E ^ 2)
      ∧ A * D * E - B * C * G ≠ 0 ∧ A * G ^ 2 - C * E ^ 2 ≠ 0 := by
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
public theorem den_addX_both_kernel {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hne : x₁ ≠ x₂) (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by grind [Affine.slope_of_X_ne]
  have haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by rw [hx3def]; simp only [Affine.addX, curve]; grind
  have hcv1 := equation_curve h₁
  have hcv2 := equation_curve h₂
  obtain ⟨E, hA, hB, hpE, hpA, hEne⟩ := kernel_point_data h₁ hd1
  obtain ⟨G, hC, hD, hpG, hpC, hGne⟩ := kernel_point_data h₂ hd2
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
  exact den_zero_of_cert (M := a₆ * E ^ 2 * G ^ 2) hMain hpA hpC hcrux
    (fun h ↦ hpA (h ▸ dvd_zero _)) (fun h ↦ hpC (h ▸ dvd_zero _)) hK0 hN0

end ECCompute
