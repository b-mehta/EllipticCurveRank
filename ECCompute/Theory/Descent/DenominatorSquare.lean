/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The denominator of an affine point is a perfect square

For the integral Weierstrass curve `E : y² = x³ + a₂x² + a₄x + a₆` over `ℚ` and a solution
`(x, y)`, this file proves there is a natural number `w` with `x.den = w²` and `y.den = w³`,
so a point is `(u/w², v/w³)` in lowest terms.

This is used in the additivity of the descent character to drop the `w²` factor
from the Legendre symbol, since a square does not change a quadratic residue class.

Clearing denominators in `y² = f(x)` with `f` integral gives `y.num² * x.den³ = N * y.den²`
for `N := x.num³ + a₂ x.num² x.den + a₄ x.num x.den² + a₆ x.den³`. Since `N ≡ x.num³` is
coprime to `x.den` and `y.num` to `y.den`, comparing sides forces `x.den³ = y.den²`, and the
coprime exponents `2, 3` yield the common witness `w`.

## Main declarations

* `ECCompute.den_isSquare`: from the affine equation, `∃ w, x.den = w² ∧ y.den = w³`.
* `ECCompute.den_isSquare_of_nonsingular`: the same for the coordinates of a point `.some x y h`.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ)

private theorem isCoprime_add_mul_left_left {R : Type*} [CommRing R] {a b : R}
    (h : IsCoprime a b) (c : R) : IsCoprime (a + b * c) b := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, v - u * c, by grind⟩

private theorem exists_sq_cube_of_cube_eq_sq {d g : ℕ} (hdg : d ^ 3 = g ^ 2) :
    ∃ w : ℕ, d = w ^ 2 ∧ g = w ^ 3 := by
  have hQ : (d : ℚ) ^ 3 = (g : ℚ) ^ 2 := by exact_mod_cast hdg
  obtain ⟨c, hc⟩ := (pow_eq_pow_iff_of_coprime (by decide : (3 : ℕ).Coprime 2)).mp hQ
  have hsq : IsSquare d := by
    rw [← Rat.isSquare_natCast_iff]
    exact ⟨c, by rw [hc.1]; grind⟩
  obtain ⟨w, hw⟩ := hsq.exists_sq
  refine ⟨w, hw, ?_⟩
  have : g ^ 2 = (w ^ 3) ^ 2 := by rw [← hdg, hw]; grind
  have := congrArg Nat.sqrt this
  rwa [Nat.sqrt_eq', Nat.sqrt_eq'] at this

/-- For a solution `(x, y)` of the integral curve `y² = x³ + a₂x² + a₄x + a₆`, there is a
natural number `w` with `x.den = w²` and `y.den = w³`. -/
theorem den_isSquare {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 := by
  have heq : y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
    have := (WeierstrassCurve.Affine.equation_iff (W := (curve a₂ a₄ a₆).toAffine) x y).mp h
    simpa [curve] using this
  have hx : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * (y.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  have key : y.num ^ 2 * (x.den : ℤ) ^ 3
      = (x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
          + a₆ * (x.den : ℤ) ^ 3) * (y.den : ℤ) ^ 2 := by
    have hQ : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3
        = ((x.num : ℚ) ^ 3 + a₂ * (x.num : ℚ) ^ 2 * x.den + a₄ * (x.num : ℚ) * (x.den : ℚ) ^ 2
            + a₆ * (x.den : ℚ) ^ 3) * (y.den : ℚ) ^ 2 := by
      rw [hx, hy]; grind
    exact_mod_cast hQ
  set N : ℤ := x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
      + a₆ * (x.den : ℤ) ^ 3 with hN
  have hcx : IsCoprime (x.num) (x.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using x.reduced
  have hcy : IsCoprime (y.num) (y.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using y.reduced
  have hcN : IsCoprime N (x.den : ℤ) := by
    have hNfac : N = x.num ^ 3 + (x.den : ℤ) *
        (a₂ * x.num ^ 2 + a₄ * x.num * x.den + a₆ * (x.den : ℤ) ^ 2) := by rw [hN]; grind
    rw [hNfac]
    exact isCoprime_add_mul_left_left hcx.pow_left _
  have hdvd1 : (x.den : ℤ) ^ 3 ∣ (y.den : ℤ) ^ 2 := by
    have hc : IsCoprime ((x.den : ℤ) ^ 3) N := (hcN.symm).pow_left
    exact hc.dvd_of_dvd_mul_left ⟨y.num ^ 2, by rw [← key]; grind⟩
  have hdvd2 : (y.den : ℤ) ^ 2 ∣ (x.den : ℤ) ^ 3 := by
    have hc : IsCoprime ((y.den : ℤ) ^ 2) (y.num ^ 2) := (hcy.symm.pow_left).pow_right
    exact hc.dvd_of_dvd_mul_left ⟨N, by rw [key]; grind⟩
  have hcube : x.den ^ 3 = y.den ^ 2 := by
    have d1 : x.den ^ 3 ∣ y.den ^ 2 := by exact_mod_cast hdvd1
    have d2 : y.den ^ 2 ∣ x.den ^ 3 := by exact_mod_cast hdvd2
    exact Nat.dvd_antisymm d1 d2
  exact exists_sq_cube_of_cube_eq_sq hcube

/-- Point form of `den_isSquare`: for a point `.some x y h` on the integral curve, there is
`w` with `x.den = w²` and `y.den = w³`. -/
theorem den_isSquare_of_nonsingular {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 :=
  den_isSquare a₂ a₄ a₆ h.1

end ECCompute
