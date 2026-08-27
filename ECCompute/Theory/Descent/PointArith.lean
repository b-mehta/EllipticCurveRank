/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character
public import Mathlib.Algebra.Field.ZMod

import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import ECCompute.ForMathlib.RatDenom
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Qify

/-!
# Reducing a rational affine point mod `p`

For the integral curve `E : y² = x³ + a₂x² + a₄x + a₆` over `ℚ` and a solution `(x, y)`: the
denominator is a perfect square (`den_isSquare`, giving `w` with `x.den = w²` and `y.den = w³`, so
a point is `(u/w², v/w³)` in lowest terms), and the coordinates cast to `ZMod p`.

## Main declarations

* `ECCompute.den_isSquare`: from the affine equation, `∃ w, x.den = w² ∧ y.den = w³`.
* `ECCompute.xbar`: the reduced `x`-coordinate `(x : ZMod p)` as a plain field element.
* `ECCompute.ydenom_eq_zero_iff`: the `y`-denominator vanishes mod `p` iff the `x`-denominator does.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}

/-- For a solution `(x, y)` of the integral curve `y² = x³ + a₂x² + a₄x + a₆`, there is a
natural number `w` with `x.den = w²` and `y.den = w³`. -/
public theorem den_isSquare {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 := by
  set N : ℤ := x.num ^ 3 + x.den * (a₂ * x.num ^ 2 + a₄ * x.num * x.den + a₆ * x.den ^ 2)
  have key : y.num ^ 2 * x.den ^ 3 = y.den ^ 2 * N := by
    qify [N]
    grind [x.mul_den_eq_num, y.mul_den_eq_num]
  have h₁ : IsCoprime ↑x.den N := x.isCoprime_num_den.symm.pow_right.add_mul_left_right _
  have heq : (x.den : ℤ) ^ 3 = y.den ^ 2 := Int.dvd_antisymm (by positivity) (by positivity)
    (h₁.pow_left.dvd_of_dvd_mul_left ⟨y.num ^ 2, by grind⟩)
    (y.isCoprime_num_den.symm.pow.dvd_of_dvd_mul_left ⟨N, key⟩)
  exact Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow (by grind) (mod_cast heq)

/-- The reduced `x`-coordinate `(x : ZMod p)` of an affine point, as a plain field element. -/
@[expose]
public noncomputable def xbar (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p := (x : ZMod p)

variable {p : ℕ}

/-- Cast identity: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` when `p ∤ x.den`. -/
public theorem num_eq_xbar_mul_den [Fact p.Prime] {x : ℚ} (hd : (x.den : ZMod p) ≠ 0) :
    x.num = xbar p x * x.den := by rw [xbar, Rat.cast_def, div_mul_cancel₀ _ hd]

/-- The `y`-denominator vanishes mod `p` iff the `x`-denominator does (since
`x.den = w²`, `y.den = w³`). -/
public theorem ydenom_eq_zero_iff (hp : p.Prime) {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    (y.den : ZMod p) = 0 ↔ (x.den : ZMod p) = 0 := by
  obtain ⟨w, hxw, hyw⟩ := den_isSquare h
  simp only [ZMod.natCast_eq_zero_iff]
  grind [hp.prime.dvd_pow_iff_dvd]

end ECCompute
