/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Reduction.IntModel
public import ECCompute.ForMathlib.RatDenom

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

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}
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
  have hx1sq : ((x₁ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1
  have hx2sq : ((x₂ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2
  have hprod : ((x₁ * x₂ : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out hd1 hd2
  have esum : ((x₁ + x₂ : ℚ).den : ZMod p) ≠ 0 := den_add_ne_zero Fact.out hd1 hd2
  have e1 := den_add_ne_zero Fact.out hx1sq hprod
  have e2 := den_add_ne_zero Fact.out e1 hx2sq
  have e3 : ((a₂ * (x₁ + x₂)).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out (by simp) esum
  have e4 := den_add_ne_zero Fact.out e2 e3
  have hd : ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄).den : ZMod p) ≠ 0 :=
    den_add_ne_zero Fact.out e4 (by simp)
  refine ⟨hd, ?_⟩
  rw [cast_add_of_ne_zero e4 (by simp), cast_add_of_ne_zero e2 e3,
    cast_add_of_ne_zero e1 hx2sq, cast_add_of_ne_zero hx1sq hprod, cast_pow,
    cast_mul_of_ne_zero hd1 hd2, cast_pow, cast_mul_of_ne_zero (by simp) esum,
    cast_add_of_ne_zero hd1 hd2, cast_intCast, cast_intCast]

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
public theorem reduced_slope_den (hne : x₁ ≠ x₂)
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
  rw [halt]
  exact den_div_ne_zero Fact.out (cast_secant_num hd1 hd2).1
    (fun h ↦ hy2' (by rw [Rat.cast_def, h, zero_div]))

/-- The reduced coordinates satisfy the reduced `addX` relation `S² = X̄₃ + a₂ + X̄₁ + X̄₂` and the
alternate-slope identity `S·(Ȳ₁ + Ȳ₂) = X̄₁² + X̄₁X̄₂ + X̄₂² + a₂(X̄₁ + X̄₂) + a₄`, for the reduced
secant slope `S = (slope …)`. -/
public theorem reduced_tangent_eqs (hne : x₁ ≠ x₂)
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
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
    simp only [Affine.addX, curve]; grind
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
public theorem slope_den_of_addX_den (hp : p.Prime)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have he : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₂ + x₁ + x₂ := by
    simp only [Affine.addX, curve]; grind
  have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [he]
    exact den_add_ne_zero hp (den_add_ne_zero hp (den_add_ne_zero hp hd3 (by simp)) hd1) hd2
  rw [den_pow, Nat.cast_pow] at hℓ2
  exact fun h ↦ hℓ2 (by grind)

/-- The doubled `x`-coordinate `addX x₁ x₂ ℓ` survives reduction when the slope, `x₁` and `x₂`
all do: `addX = ℓ² - a₂ - x₁ - x₂` has nonzero denominator mod `p`. -/
public theorem addX_den_ne (hp : p.Prime) {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [haddX]
  exact den_sub_ne_zero hp (den_sub_ne_zero hp (den_sub_ne_zero hp
    (by rw [den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hℓden) (by simp)) hd1) hd2

section
variable [Fact p.Prime]

/-! ### The reduced addition formulas -/

/-- In the genuine-tangent case the reduced secant slope equals the reduced tangent slope `ℓ`:
`slope X̄₁ X̄₁ Ȳ₁ Ȳ₁ = ℓ`, matched via the reduced tangent identity `htan` and `X̄₁ = X̄₂`. -/
public theorem reduced_slope_eq {ℓ : ZMod p} {x₁ x₂ y₁ y₂ : ZMod p}
    (hYneg : ¬ y₁ = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁)
    (h2Yne : y₁ + y₁ ≠ 0) (hXbar : x₁ = x₂) (hYbar : y₁ = y₂)
    (htan : ℓ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄) :
    (curveZMod a₂ a₄ a₆ p).toAffine.slope x₁ x₁ y₁ y₁ = ℓ := by
  refine mul_right_cancel₀ h2Yne ?_
  rw [Affine.slope_of_Y_ne rfl hYneg]
  simp only [map_curveℤ_zmod, Affine.negY, zero_mul, sub_zero, sub_neg_eq_add]
  rw [div_mul_cancel₀ _ h2Yne]
  grind

/-- The reduced-curve `addX` at a doubled point unfolds to `L² - a₂ - X - X`. -/
public theorem reduced_addX_eq {X L : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.addX X X L = L ^ 2 - a₂ - X - X := by
  simp only [Affine.addX, map_curveℤ_zmod]; grind

/-- The reduced-curve `addY` at a doubled point unfolds to `-(ℓ·(addX - X̄₁) + Ȳ₁)`. -/
public theorem reduced_addY_eq {X Y L : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.addY X X Y L
      = -(L * ((curveZMod a₂ a₄ a₆ p).toAffine.addX X X L - X) + Y) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY, map_curveℤ_zmod]; grind

/-- When the slope, `x`-coordinates and `y`-coordinate have nonzero denominators mod `p`, the cast
of the rational `addY` equals `-(ℓ·(addX - x₁) + y₁)` over `ZMod p`. -/
public theorem addY_cast_eq {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
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

end ECCompute
