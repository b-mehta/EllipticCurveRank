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
private theorem cast_secant_num (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0) :
    ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)).den : ZMod p) ≠ 0
      ∧ ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) : ℚ) : ZMod p)
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  have hx1sq : ((x₁ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1
  have hx2sq : ((x₂ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2
  have hprod : ((x₁ * x₂ : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero hd1 hd2
  have esum : ((x₁ + x₂ : ℚ).den : ZMod p) ≠ 0 := den_add_ne_zero hd1 hd2
  have e1 := den_add_ne_zero hx1sq hprod
  have e2 := den_add_ne_zero e1 hx2sq
  have e3 : (((a₂ : ℚ) * (x₁ + x₂)).den : ZMod p) ≠ 0 := den_mul_ne_zero (by simp) esum
  have e4 := den_add_ne_zero e2 e3
  have hd : ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)).den : ZMod p) ≠ 0 :=
    den_add_ne_zero e4 (by simp)
  refine ⟨hd, ?_⟩
  rw [Rat.cast_add_of_ne_zero e4 (by simp), Rat.cast_add_of_ne_zero e2 e3,
    Rat.cast_add_of_ne_zero e1 hx2sq, Rat.cast_add_of_ne_zero hx1sq hprod, Rat.cast_pow,
    Rat.cast_mul_of_ne_zero hd1 hd2, Rat.cast_pow, Rat.cast_mul_of_ne_zero (by simp) esum,
    Rat.cast_add_of_ne_zero hd1 hd2, Rat.cast_intCast, Rat.cast_intCast]

/-- The reduced secant slope times `y₁ + y₂` equals the secant numerator: clearing the denominator
of `slope = (y₁ - y₂)/(x₁ - x₂)` against the two curve relations gives
`slope·(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄`. -/
private theorem slope_mul_add_eq (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂) :
    (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂)
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
  have hcv1 := equation_curve a₂ a₄ a₆ h₁
  have hcv2 := equation_curve a₂ a₄ a₆ h₂
  have hℓ : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne]; grind
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
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
    (hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← Rat.cast_add_of_ne_zero hdy1 hdy2, h0, Rat.cast_zero]
  have halt : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by rwa [Rat.cast_add_of_ne_zero hdy1 hdy2]
  have hNden := (cast_secant_num a₂ a₄ p hd1 hd2).1
  rw [halt]
  exact den_div_ne_zero hNden (den_add_ne_zero hdy1 hdy2) hy2'

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
        = ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ZMod p)
          + (a₂ : ZMod p) + (x₁ : ZMod p) + (x₂ : ZMod p)
      ∧ ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) * ((y₁ : ZMod p) + (y₂ : ZMod p))
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
      grind
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rw [Rat.cast_pow,
      Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero hd3 (by simp)) hd1,
      Rat.cast_add_of_ne_zero hd3 (by simp), Rat.cast_intCast] at hc
    exact hc
  · have hℓmul : ℓ * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
      rw [hℓdef]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rw [Rat.cast_mul_of_ne_zero hℓden (den_add_ne_zero hdy1 hdy2),
      Rat.cast_add_of_ne_zero hdy1 hdy2, (cast_secant_num a₂ a₄ p hd1 hd2).2] at hc
    exact hc

/-- If the doubled `x`-coordinate `addX x₁ x₂ (slope …)` survives reduction, so does the slope:
from `ℓ² = addX + a₂ + x₁ + x₂` a nonzero `addX`-denominator forces a nonzero `ℓ`-denominator. -/
theorem slope_den_of_addX_den
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have he : (ℓ : ℚ) ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [he]; exact den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2
  rw [Rat.den_pow, Nat.cast_pow] at hℓ2
  exact fun h => hℓ2 (by grind)

/-- The doubled `x`-coordinate `addX x₁ x₂ ℓ` survives reduction when the slope, `x₁` and `x₂`
all do: `addX = ℓ² - a₂ - x₁ - x₂` has nonzero denominator mod `p`. -/
theorem addX_den_ne {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
  rw [haddX]
  exact den_sub_ne_zero (den_sub_ne_zero (den_sub_ne_zero
    (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hℓden) (by simp)) hd1) hd2

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
theorem reduced_addX_eq (X L : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L
      = L ^ 2 - (a₂ : ZMod p) - X - X := by
  simp only [WeierstrassCurve.Affine.addX, map_curveℤ_zmod]; grind

/-- The reduced-curve `addY` at a doubled point unfolds to `-(ℓ·(addX - X̄₁) + Ȳ₁)`. -/
theorem reduced_addY_eq (X Y L : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addY X X Y L
      = -(L * (((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L - X)
        + Y) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, map_curveℤ_zmod]; grind

/-- The cast of the rational `addY` matches the reduced `addY` form when the slope, `x`-coordinates
and `y`-coordinate all survive reduction: the denominators of each summand are nonzero mod `p`, so
`Rat.cast` distributes over the `-(ℓ·(addX - x₁) + y₁)` expression. -/
theorem addY_cast_eq {x₁ y₁ x₂ ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hdy1 : (y₁.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0) :
    ((curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
      = -((ℓ : ZMod p) * (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p) - (x₁ : ZMod p))
        + (y₁ : ZMod p)) := by
  have haddY : (curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, curve]; grind
  rw [haddY, Rat.cast_neg,
    Rat.cast_add_of_ne_zero (den_mul_ne_zero hℓden (den_sub_ne_zero hd3 hd1)) hdy1,
    Rat.cast_mul_of_ne_zero hℓden (den_sub_ne_zero hd3 hd1), Rat.cast_sub_of_ne_zero hd3 hd1]

end ECCompute
