/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.IntModel
import ECCompute.ForMathlib.RatDenom

/-!
# Denominators of the group law survive reduction

For two affine points of `curve a₂ a₄ a₆` whose coordinates have `p`-unit denominators, this file
tracks the denominators of the secant slope and of the sum through reduction mod `p`, and matches
the reduced coordinates against the addition formulas of the reduced curve.

The secant slope `(y₁ - y₂)/(x₁ - x₂)` is a `0/0` mod `p` exactly when `X̄₁ = X̄₂`; the alternate
form `(x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄)/(y₁ + y₂)` has the same value and a denominator that
survives whenever `Ȳ₁ + Ȳ₂ ≠ 0`.

## Main declarations

* `ECCompute.reduced_slope_den`, `ECCompute.slope_den_of_addX_den`, `ECCompute.addX_den_ne`:
  survival of the slope and `addX` denominators.
* `ECCompute.reduced_tangent_eqs`: the two reduced identities satisfied by the secant slope.
* `ECCompute.reduced_slope_eq`, `ECCompute.reduced_addX_eq`, `ECCompute.reduced_addY_eq`,
  `ECCompute.addY_cast_eq`: the reduced coordinates in terms of the doubling formulas.
-/

open WeierstrassCurve

namespace ECCompute

open Rat

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]
variable {x₁ y₁ x₂ y₂ : ℚ}

/-! ### The reduced secant slope -/

/-- The secant numerator `x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄` has good denominator, and its
reduction is the corresponding polynomial in `X̄₁, X̄₂`. -/
private theorem cast_secant_num (hd1 : IsPIntegral p x₁) (hd2 : IsPIntegral p x₂) :
    IsPIntegral p (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ))
      ∧ ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) : ℚ) : ZMod p)
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  have hx1sq : IsPIntegral p (x₁ ^ 2) := pow_mem hd1 2
  have hx2sq : IsPIntegral p (x₂ ^ 2) := pow_mem hd2 2
  have hprod : IsPIntegral p (x₁ * x₂) := mul_mem hd1 hd2
  have esum : IsPIntegral p (x₁ + x₂) := add_mem hd1 hd2
  have ha2 : IsPIntegral p (a₂ : ℚ) := intCast_pIntegral a₂
  have e1 : IsPIntegral p (x₁ ^ 2 + x₁ * x₂) := add_mem hx1sq hprod
  have e2 : IsPIntegral p (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) := add_mem e1 hx2sq
  have e3 : IsPIntegral p ((a₂ : ℚ) * (x₁ + x₂)) := mul_mem ha2 esum
  have e4 : IsPIntegral p (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂)) := add_mem e2 e3
  refine ⟨add_mem e4 (intCast_pIntegral a₄), ?_⟩
  rw [cast_add_of_pIntegral e4 (intCast_pIntegral a₄), cast_add_of_pIntegral e2 e3,
    cast_add_of_pIntegral e1 hx2sq, cast_add_of_pIntegral hx1sq hprod, Rat.cast_pow,
    cast_mul_of_pIntegral hd1 hd2, Rat.cast_pow, cast_mul_of_pIntegral ha2 esum,
    cast_add_of_pIntegral hd1 hd2, Rat.cast_intCast, Rat.cast_intCast]

/-- For the reduced secant slope, `slope·(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄`. -/
private theorem slope_mul_add_eq (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂) :
    (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂)
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
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
    (hd1 : IsPIntegral p x₁) (hd2 : IsPIntegral p x₂)
    (hdy1 : IsPIntegral p y₁) (hdy2 : IsPIntegral p y₂)
    (hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0) :
    IsPIntegral p ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) := by
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← cast_add_of_pIntegral hdy1 hdy2, h0, Rat.cast_zero]
  have halt : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by rwa [cast_add_of_pIntegral hdy1 hdy2]
  have hNden := (cast_secant_num a₂ a₄ p hd1 hd2).1
  rw [halt, div_eq_mul_inv]
  exact mul_mem hNden (inv_pIntegral (add_mem hdy1 hdy2) hy2')

/-- The reduced coordinates satisfy the reduced `addX` relation `S² = X̄₃ + a₂ + X̄₁ + X̄₂` and the
alternate-slope identity `S·(Ȳ₁ + Ȳ₂) = X̄₁² + X̄₁X̄₂ + X̄₂² + a₂(X̄₁ + X̄₂) + a₄`, for the reduced
secant slope `S = (slope …)`. -/
theorem reduced_tangent_eqs (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : IsPIntegral p x₁) (hd2 : IsPIntegral p x₂)
    (hdy1 : IsPIntegral p y₁) (hdy2 : IsPIntegral p y₂)
    (hℓden : IsPIntegral p ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂))
    (hd3 : IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂))) :
    ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) ^ 2
        = ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ZMod p)
          + (a₂ : ZMod p) + (x₁ : ZMod p) + (x₂ : ZMod p)
      ∧ ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) * ((y₁ : ZMod p) + (y₂ : ZMod p))
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have ha2 : IsPIntegral p (a₂ : ℚ) := intCast_pIntegral a₂
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
      grind
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rwa [Rat.cast_pow,
      cast_add_of_pIntegral (add_mem (add_mem hd3 ha2) hd1) hd2,
      cast_add_of_pIntegral (add_mem hd3 ha2) hd1,
      cast_add_of_pIntegral hd3 ha2, Rat.cast_intCast] at hc
  · have hℓmul : ℓ * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
      rw [hℓdef]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rwa [cast_mul_of_pIntegral hℓden (add_mem hdy1 hdy2),
      cast_add_of_pIntegral hdy1 hdy2, (cast_secant_num a₂ a₄ p hd1 hd2).2] at hc

/-- If the doubled `x`-coordinate `addX x₁ x₂ (slope …)` has nonzero denominator mod `p`, then so
does the slope. -/
theorem slope_den_of_addX_den
    (hd1 : IsPIntegral p x₁) (hd2 : IsPIntegral p x₂)
    (hd3 : IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂))) :
    IsPIntegral p ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have ha2 : IsPIntegral p (a₂ : ℚ) := intCast_pIntegral a₂
  have he : (ℓ : ℚ) ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hℓ2 : IsPIntegral p (ℓ ^ 2) := by
    rw [he]; exact add_mem (add_mem (add_mem hd3 ha2) hd1) hd2
  rw [Rat.mem_padicInteger_iff, Rat.den_pow, Nat.cast_pow] at hℓ2
  rw [Rat.mem_padicInteger_iff]
  exact fun h ↦ hℓ2 (by grind)

/-- The doubled `x`-coordinate `addX x₁ x₂ ℓ` survives reduction when the slope, `x₁` and `x₂`
all do: `addX = ℓ² - a₂ - x₁ - x₂` has nonzero denominator mod `p`. -/
theorem addX_den_ne {ℓ : ℚ} (hℓden : IsPIntegral p ℓ)
    (hd1 : IsPIntegral p x₁) (hd2 : IsPIntegral p x₂)
    (haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂) :
    IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ) := by
  rw [haddX]
  exact sub_mem (sub_mem (sub_mem (pow_mem hℓden 2) (intCast_pIntegral a₂)) hd1) hd2

/-! ### The reduced addition formulas -/

/-- In the genuine-tangent case the reduced secant slope equals the reduced tangent slope `ℓ`:
`slope X̄₁ X̄₁ Ȳ₁ Ȳ₁ = ℓ`, matched via the reduced tangent identity `htan` and `X̄₁ = X̄₂`. -/
theorem reduced_slope_eq {ℓ : ZMod p} {x₁ x₂ y₁ y₂ : ZMod p}
    (hYneg : ¬ y₁ = ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY x₁ y₁)
    (h2Yne : y₁ + y₁ ≠ 0) (hXbar : x₁ = x₂) (hYbar : y₁ = y₂)
    (htan : ℓ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.slope x₁ x₁ y₁ y₁ = ℓ := by
  refine mul_right_cancel₀ h2Yne ?_
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYneg]
  simp only [map_curveℤ_zmod, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add]
  rw [div_mul_cancel₀ _ h2Yne]
  grind

/-- The reduced-curve `addX` at a doubled point unfolds to `L² - a₂ - X - X`. -/
theorem reduced_addX_eq {X L : ZMod p} :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L
      = L ^ 2 - (a₂ : ZMod p) - X - X := by
  simp only [WeierstrassCurve.Affine.addX, map_curveℤ_zmod]; grind

/-- The reduced-curve `addY` at a doubled point unfolds to `-(ℓ·(addX - X̄₁) + Ȳ₁)`. -/
theorem reduced_addY_eq {X Y L : ZMod p} :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addY X X Y L
      = -(L * (((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L - X)
        + Y) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, map_curveℤ_zmod]; grind

/-- When the slope, `x`-coordinates and `y`-coordinate have nonzero denominators mod `p`, the cast
of the rational `addY` equals `-(ℓ·(addX - x₁) + y₁)` over `ZMod p`. -/
theorem addY_cast_eq {x₁ y₁ x₂ ℓ : ℚ} (hℓden : IsPIntegral p ℓ)
    (hd1 : IsPIntegral p x₁) (hdy1 : IsPIntegral p y₁)
    (hd3 : IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ)) :
    ((curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
      = -((ℓ : ZMod p) * (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p) - (x₁ : ZMod p))
        + (y₁ : ZMod p)) := by
  have haddY : (curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, curve]; grind
  rw [haddY, Rat.cast_neg,
    cast_add_of_pIntegral (mul_mem hℓden (sub_mem hd3 hd1)) hdy1,
    cast_mul_of_pIntegral hℓden (sub_mem hd3 hd1), cast_sub_of_pIntegral hd3 hd1]

end ECCompute
