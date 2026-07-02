import ECCompute.Descent
import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The denominator of an affine point is a perfect square

For the integral Weierstrass curve `E : y² = x³ + a₂x² + a₄x + a₆` over `ℚ` and an affine
point `P = (x, y)` on `E`, this file proves that `x.den` is a perfect square.  Concretely
there is a natural number `w` with `x.den = w²` and `y.den = w³`, so `P = (u/w², v/w³)` in
lowest terms.

This is ticket **T1a**, a prerequisite for the additivity of the descent character: it lets
the `w²` factor be dropped from the Legendre symbol, since a square never changes a
quadratic residue class.

## Proof outline

Clearing denominators in `y² = f(x)` and using that `f` has integer coefficients gives the
integer identity
  `y.num² · x.den³ = N · y.den²`,   `N := x.num³ + a₂ x.num² x.den + a₄ x.num x.den² + a₆ x.den³`.
Because `gcd(x.num, x.den) = 1`, the integer `N ≡ x.num³` is coprime to `x.den`, and
likewise `gcd(y.num, y.den) = 1`.  Comparing the two sides forces `x.den³ = y.den²`.  Two
coprime exponents then pin down the shape: `x.den` is a square and `y.den` a cube of a
common `w`.

## Main declarations

* `ECCompute.den_isSquare` — from the affine equation, `∃ w, x.den = w² ∧ y.den = w³`.
* `ECCompute.den_isSquare_of_nonsingular` — the same for the coordinates of a point `.some x y h`.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ)

/-- Adding a multiple of `b` to `a` preserves coprimality with `b`. -/
private theorem isCoprime_add_mul_left_left {R : Type*} [CommRing R] {a b : R}
    (h : IsCoprime a b) (c : R) : IsCoprime (a + b * c) b := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, v - u * c, by linear_combination huv⟩

/-- If `d³ = g²` for positive naturals, then `d` is a perfect square and `g` a perfect cube
with a common witness: `∃ w, d = w² ∧ g = w³`. -/
private theorem exists_sq_cube_of_cube_eq_sq {d g : ℕ} (hdg : d ^ 3 = g ^ 2) :
    ∃ w : ℕ, d = w ^ 2 ∧ g = w ^ 3 := by
  have hQ : (d : ℚ) ^ 3 = (g : ℚ) ^ 2 := by exact_mod_cast hdg
  obtain ⟨c, hc⟩ := (pow_eq_pow_iff_of_coprime (by decide : (3 : ℕ).Coprime 2)).mp hQ
  have hsq : IsSquare d := by
    rw [← Rat.isSquare_natCast_iff]
    exact ⟨c, by rw [hc.1]; ring⟩
  obtain ⟨w, hw⟩ := hsq.exists_sq
  refine ⟨w, hw, ?_⟩
  have : g ^ 2 = (w ^ 3) ^ 2 := by rw [← hdg, hw]; ring
  have := congrArg Nat.sqrt this
  rwa [Nat.sqrt_eq', Nat.sqrt_eq'] at this

/-- **The denominator of an affine point is a perfect square.**  For the integral curve
`y² = x³ + a₂x² + a₄x + a₆` and a solution `(x, y)`, there is a natural number `w` with
`x.den = w²` and `y.den = w³`. -/
theorem den_isSquare {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 := by
  -- The affine equation with `a₁ = a₃ = 0`.
  have heq : y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
    have := (WeierstrassCurve.Affine.equation_iff (W := (curve a₂ a₄ a₆).toAffine) x y).mp h
    simpa [curve] using this
  -- `num = coordinate · den`.
  have hx : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * (y.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  -- Clear denominators to an integer identity.
  have key : y.num ^ 2 * (x.den : ℤ) ^ 3
      = (x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
          + a₆ * (x.den : ℤ) ^ 3) * (y.den : ℤ) ^ 2 := by
    have hQ : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3
        = ((x.num : ℚ) ^ 3 + a₂ * (x.num : ℚ) ^ 2 * x.den + a₄ * (x.num : ℚ) * (x.den : ℚ) ^ 2
            + a₆ * (x.den : ℚ) ^ 3) * (y.den : ℚ) ^ 2 := by
      rw [hx, hy]; linear_combination ((x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2) * heq
    exact_mod_cast hQ
  set N : ℤ := x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
      + a₆ * (x.den : ℤ) ^ 3 with hN
  -- Coprimality inputs.
  have hcx : IsCoprime (x.num) (x.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using x.reduced
  have hcy : IsCoprime (y.num) (y.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using y.reduced
  have hcN : IsCoprime N (x.den : ℤ) := by
    rw [hN, show x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
          + a₆ * (x.den : ℤ) ^ 3
        = x.num ^ 3 + (x.den : ℤ) * (a₂ * x.num ^ 2 + a₄ * x.num * x.den
          + a₆ * (x.den : ℤ) ^ 2) from by ring]
    exact isCoprime_add_mul_left_left (hcx.pow_left) _
  -- Two-sided divisibility `x.den³ = y.den²`.
  have hdvd1 : (x.den : ℤ) ^ 3 ∣ (y.den : ℤ) ^ 2 := by
    have hc : IsCoprime ((x.den : ℤ) ^ 3) N := (hcN.symm).pow_left
    exact hc.dvd_of_dvd_mul_left ⟨y.num ^ 2, by rw [← key]; ring⟩
  have hdvd2 : (y.den : ℤ) ^ 2 ∣ (x.den : ℤ) ^ 3 := by
    have hc : IsCoprime ((y.den : ℤ) ^ 2) (y.num ^ 2) := (hcy.symm.pow_left).pow_right
    exact hc.dvd_of_dvd_mul_left ⟨N, by rw [key]; ring⟩
  have hcube : x.den ^ 3 = y.den ^ 2 := by
    have d1 : x.den ^ 3 ∣ y.den ^ 2 := by exact_mod_cast hdvd1
    have d2 : y.den ^ 2 ∣ x.den ^ 3 := by exact_mod_cast hdvd2
    exact Nat.dvd_antisymm d1 d2
  exact exists_sq_cube_of_cube_eq_sq hcube

/-- **The denominator of an affine point is a perfect square** (point form).  For a point
`.some x y h` on the integral curve `y² = x³ + a₂x² + a₄x + a₆`, there is `w` with
`x.den = w²` and `y.den = w³`. -/
theorem den_isSquare_of_nonsingular {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 :=
  den_isSquare a₂ a₄ a₆ h.1

end ECCompute
