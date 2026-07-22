/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.Theory.Descent.Collinearity
import ECCompute.ForMathlib.RatDenom
import ECCompute.ForMathlib.WeierstrassCurveAffine
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.ZMod

/-!
# Elementary reduction arithmetic

Elementary lemmas about pushing `Rat.cast : ℚ → ZMod p` through the group law when denominators
survive reduction, shared between `ECCompute.Descent` and `ECCompute.Descent.Reduction.Hom`.

## Main declarations

* `ECCompute.xbar`: the reduced `x`-coordinate `(x : ZMod p)` as a plain field element.
* `ECCompute.num_eq_xbar_mul_den`: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` when `p ∤ x.den`.
* `ECCompute.reduced_on_curve` / `reduced_addX` / `reduced_doubleX`: the reduced on-curve, secant
  and tangent identities, obtained by clearing denominators to an integer identity.
* `ECCompute.den_dblX_ne_zero` / `ydenom_ne_zero`: good-denominator survival for the doubled
  `x`-coordinate and for the `y`-coordinate.
-/

open WeierstrassCurve

namespace ECCompute

open Rat (den_add_ne_zero den_sub_ne_zero den_mul_ne_zero den_pow_ne_zero den_div_ne_zero)

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### Reducing `x` to `ZMod p`

For `P = (x, y)` on `E` with `p ∤ x.den`, write `X := (x : ZMod p)` (the rational cast) and
`w` with `x.den = w²`. Then `α = x.num - θ·x.den = w²·(X - θ)`. -/

/-- The reduced `x`-coordinate `(x : ZMod p)` of an affine point, as a plain field element. -/
noncomputable def xbar (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p := (x : ZMod p)

variable {a₂ a₄ a₆ p}

/-- Cast identity: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` when `p ∤ x.den`. -/
theorem num_eq_xbar_mul_den [Fact p.Prime] {x : ℚ} (hd : (x.den : ZMod p) ≠ 0) :
    (x.num : ZMod p) = xbar p x * (x.den : ZMod p) := by
  rw [xbar, Rat.cast_def, div_mul_cancel₀ _ hd]

/-! ### Elementary reduction mod `p`

`Rat.cast : ℚ → ZMod p` is *not* a ring homomorphism in characteristic `p`. In the
*good-reduction* case we transfer group-law data to `ZMod p` by clearing denominators via the
genuine ring hom `Int.cast`, pushing `Rat.cast` through sums/products whose denominators survive
reduction (`(·.den : ZMod p) ≠ 0`) with the conditional cast lemmas; the good-denominator closure
lemmas `Rat.den_add_ne_zero` and friends (from `ECCompute.ForMathlib.RatDenom`) supply survival of
this predicate. -/

/-- A ℚ-point `(x, y)` on `E` with good denominators reduces to a point of `E` over `ZMod p`. -/
theorem reduced_on_curve [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y)
    (hdx : (x.den : ZMod p) ≠ 0) (hdy : (y.den : ZMod p) ≠ 0) :
    (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + (a₂ : ZMod p) * (x : ZMod p) ^ 2
      + (a₄ : ZMod p) * (x : ZMod p) + (a₆ : ZMod p) := by
  have heq : y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
    grind [WeierstrassCurve.Affine.equation_iff, curve]
  have hx : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * (y.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  have key : (y.num ^ 2 * (x.den : ℤ) ^ 3 : ℤ)
      = (x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
          + a₆ * (x.den : ℤ) ^ 3) * (y.den : ℤ) ^ 2 := by
    have hQ : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3
        = ((x.num : ℚ) ^ 3 + a₂ * (x.num : ℚ) ^ 2 * x.den + a₄ * (x.num : ℚ) * (x.den : ℚ) ^ 2
            + a₆ * (x.den : ℚ) ^ 3) * (y.den : ℚ) ^ 2 := by
      grind
    exact_mod_cast hQ
  have keyZ : (y.num : ZMod p) ^ 2 * (x.den : ZMod p) ^ 3
      = ((x.num : ZMod p) ^ 3 + (a₂ : ZMod p) * (x.num : ZMod p) ^ 2 * (x.den : ZMod p)
          + (a₄ : ZMod p) * (x.num : ZMod p) * (x.den : ZMod p) ^ 2
          + (a₆ : ZMod p) * (x.den : ZMod p) ^ 3) * (y.den : ZMod p) ^ 2 := by
    have := congrArg (Int.cast : ℤ → ZMod p) key
    push_cast at this
    grind
  grind [Rat.cast_def]

/-- For `x₁ ≠ x₂` and good denominators, the ℚ identity
`(x₃ + a₂ + x₁ + x₂)(x₁ - x₂)² = (y₁ - y₂)²` (with `x₃ = addX x₁ x₂ (slope …)`) reduces
mod `p`. -/
theorem reduced_addX [Fact p.Prime] {x₁ x₂ y₁ y₂ : ℚ} (hne : x₁ ≠ x₂)
    (hdx1 : (x₁.den : ZMod p) ≠ 0) (hdx2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ZMod p)
      + (a₂ : ZMod p) + (x₁ : ZMod p) + (x₂ : ZMod p)) * ((x₁ : ZMod p) - (x₂ : ZMod p)) ^ 2
      = ((y₁ : ZMod p) - (y₂ : ZMod p)) ^ 2 := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    grind [WeierstrassCurve.Affine.slope_of_X_ne]
  have haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
    grind [WeierstrassCurve.Affine.addX, curve]
  have REL : (x₃ + (a₂ : ℚ) + x₁ + x₂) * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 := by
    grind
  have hcast : (((x₃ + (a₂ : ℚ) + x₁ + x₂) * (x₁ - x₂) ^ 2 : ℚ) : ZMod p)
      = (((y₁ - y₂) ^ 2 : ℚ) : ZMod p) := by rw [REL]
  rw [Rat.cast_mul_of_ne_zero
        (den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hdx3 (by simp)) hdx1) hdx2)
        (den_pow_ne_zero (den_sub_ne_zero hdx1 hdx2) 2),
      Rat.cast_pow, Rat.cast_pow,
      Rat.cast_sub_of_ne_zero hdx1 hdx2,
      Rat.cast_sub_of_ne_zero hdy1 hdy2] at hcast
  rw [Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hdx3 (by simp)) hdx1) hdx2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero hdx3 (by simp)) hdx1,
      Rat.cast_add_of_ne_zero hdx3 (by simp)] at hcast
  rwa [Rat.cast_intCast] at hcast

/-- Casting the derivative polynomial `f'(x) = 3x² + 2a₂x + a₄` commutes with reduction when
`p ∤ x.den`. Used by `reduced_doubleX`. -/
theorem cast_fderivPoly [Fact p.Prime] {x : ℚ} (hdx : (x.den : ZMod p) ≠ 0) :
    (((3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ) : ℚ)) : ZMod p)
      = 3 * (x : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x : ZMod p) + (a₄ : ZMod p) := by
  have hx2 : ((x ^ 2).den : ZMod p) ≠ 0 := den_pow_ne_zero hdx 2
  have h3x2 : (((3 : ℚ) * x ^ 2).den : ZMod p) ≠ 0 := den_mul_ne_zero (by simp) hx2
  have h2a2 : (((2 : ℚ) * (a₂ : ℚ)).den : ZMod p) ≠ 0 := den_mul_ne_zero (by simp) (by simp)
  have h2a2x : (((2 : ℚ) * (a₂ : ℚ) * x).den : ZMod p) ≠ 0 := den_mul_ne_zero h2a2 hdx
  rw [Rat.cast_add_of_ne_zero (den_add_ne_zero h3x2 h2a2x) (by simp),
      Rat.cast_add_of_ne_zero h3x2 h2a2x,
      Rat.cast_mul_of_ne_zero (by simp) hx2, Rat.cast_pow,
      Rat.cast_mul_of_ne_zero h2a2 hdx,
      Rat.cast_mul_of_ne_zero (by simp) (by simp)]
  push_cast
  grind

/-- On `curve a₂ a₄ a₆`, `negY x y = -y` (the curve has `a₁ = a₃ = 0`). -/
theorem negY_curve (x y : ℚ) : (curve a₂ a₄ a₆).toAffine.negY x y = -y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl x y

/-- On `curve a₂ a₄ a₆`, `y ≠ negY x y` whenever `y ≠ 0`. -/
theorem y_ne_negY {x y : ℚ} (hy0 : y ≠ 0) : y ≠ (curve a₂ a₄ a₆).toAffine.negY x y := by
  grind [negY_curve]

/-- Doubling analogue of `reduced_addX`: for a point `(x, y)` with `y ≠ 0` and good denominators
(including the doubled `x`-coordinate `x₃ = dblX`), the `ℓ`-free tangent identity
`(x₃ + a₂ + 2x)·(2y)² = (3x² + 2a₂x + a₄)²` reduces mod `p`. -/
theorem reduced_doubleX [Fact p.Prime] {x y : ℚ} (hy0 : y ≠ 0)
    (hdx : (x.den : ZMod p) ≠ 0) (hdy : (y.den : ZMod p) ≠ 0)
    (hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x x
      ((curve a₂ a₄ a₆).toAffine.slope x x y y)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x x
        ((curve a₂ a₄ a₆).toAffine.slope x x y y) : ZMod p)
      + (a₂ : ZMod p) + 2 * (x : ZMod p)) * (2 * (y : ZMod p)) ^ 2
      = (3 * (x : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x : ZMod p) + (a₄ : ZMod p)) ^ 2 := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x x y y with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x x ℓ
  have hℓ : ℓ * (2 * y) = 3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ) := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_Y_ne rfl (y_ne_negY hy0), negY_curve]
    grind [curve]
  have haddX : x₃ = ℓ ^ 2 - (a₂ : ℚ) - 2 * x := by
    grind [WeierstrassCurve.Affine.addX, curve]
  have REL : (x₃ + (a₂ : ℚ) + 2 * x) * (2 * y) ^ 2
      = (3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ)) ^ 2 := by
    grind
  have hL : (((x₃ + (a₂ : ℚ) + 2 * x) * (2 * y) ^ 2 : ℚ) : ZMod p)
      = ((x₃ : ZMod p) + (a₂ : ZMod p) + 2 * (x : ZMod p)) * (2 * (y : ZMod p)) ^ 2 := by
    rw [Rat.cast_mul_of_ne_zero
          (den_add_ne_zero (den_add_ne_zero hdx3 (by simp)) (den_mul_ne_zero (by simp) hdx))
          (den_pow_ne_zero (den_mul_ne_zero (by simp) hdy) 2),
        Rat.cast_pow, Rat.cast_mul_of_ne_zero (by simp) hdy,
        Rat.cast_add_of_ne_zero (den_add_ne_zero hdx3 (by simp)) (den_mul_ne_zero (by simp) hdx),
        Rat.cast_add_of_ne_zero hdx3 (by simp),
        Rat.cast_mul_of_ne_zero (by simp) hdx, Rat.cast_intCast]
    push_cast
    grind
  have hR : (((3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ)) ^ 2 : ℚ) : ZMod p)
      = (3 * (x : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x : ZMod p) + (a₄ : ZMod p)) ^ 2 := by
    rw [Rat.cast_pow, cast_fderivPoly hdx]
  rw [← hL, ← hR]
  exact_mod_cast congrArg (Rat.cast : ℚ → ZMod p) REL

/-- The doubled `x`-coordinate has good denominator when `P = (x, y)` reduces to a
non-`2`-torsion point (`p ∤ x.den, y.den` and `Y ≠ 0`): the reduced tangent slope
`f'(x)/(2y)` has good denominator (`den_div_ne_zero`), and `dblX = ℓ² - a₂ - 2x`. -/
theorem den_dblX_ne_zero [Fact p.Prime] {x y : ℚ} (hyℚ : y ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hdx : (x.den : ZMod p) ≠ 0) (hdy : (y.den : ZMod p) ≠ 0) (hy0 : (y : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x x
        ((curve a₂ a₄ a₆).toAffine.slope x x y y)).den : ZMod p) ≠ 0 := by
  have hslopeval : (curve a₂ a₄ a₆).toAffine.slope x x y y
      = (3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ)) / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (y_ne_negY hyℚ), negY_curve]
    grind [curve]
  have hx2 : ((x ^ 2).den : ZMod p) ≠ 0 := den_pow_ne_zero hdx 2
  have hdnum : ((3 * x ^ 2 + 2 * (a₂ : ℚ) * x + (a₄ : ℚ)).den : ZMod p) ≠ 0 :=
    den_add_ne_zero (den_add_ne_zero (den_mul_ne_zero (by simp) hx2)
      (den_mul_ne_zero (den_mul_ne_zero (by simp) (by simp)) hdx)) (by simp)
  have hden2y : ((2 * y : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero (by simp) hdy
  have hcast2y : ((2 * y : ℚ) : ZMod p) ≠ 0 := by
    rw [Rat.cast_mul_of_ne_zero (by simp) hdy]; push_cast; exact mul_ne_zero h2 hy0
  have hdℓ : (((curve a₂ a₄ a₆).toAffine.slope x x y y).den : ZMod p) ≠ 0 := by
    rw [hslopeval]; exact den_div_ne_zero hdnum hden2y hcast2y
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x x ((curve a₂ a₄ a₆).toAffine.slope x x y y)
      = (curve a₂ a₄ a₆).toAffine.slope x x y y ^ 2 - (a₂ : ℚ) - x - x := by
    grind [WeierstrassCurve.Affine.addX, curve]
  rw [haddX]
  exact den_sub_ne_zero (den_sub_ne_zero (den_sub_ne_zero
    (den_pow_ne_zero hdℓ 2) (by simp)) hdx) hdx

/-- The `y`-denominator reduces well whenever the `x`-denominator does (since
`x.den = w²`, `y.den = w³`). -/
theorem ydenom_ne_zero [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hdx : (x.den : ZMod p) ≠ 0) :
    (y.den : ZMod p) ≠ 0 := by
  obtain ⟨w, hxw, hyw⟩ := den_isSquare a₂ a₄ a₆ h
  have hw : (w : ZMod p) ≠ 0 := mt (Rat.den_cast_eq_zero_iff two_ne_zero hxw).mpr hdx
  rw [hyw]
  grind

end ECCompute
