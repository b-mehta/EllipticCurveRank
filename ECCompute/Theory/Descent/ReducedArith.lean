/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Defs
public import ECCompute.ForMathlib.RatDenom

import ECCompute.Theory.Descent.DenominatorSquare
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.ZMod

/-!
# Elementary reduction arithmetic

Elementary lemmas for reducing an affine point of `curve a₂ a₄ a₆` mod `p`: the cast of the
`x`-coordinate, and survival of denominators under reduction, shared between `ECCompute.Descent`
and `ECCompute.Descent.Reduction.Hom`.

## Main declarations

* `ECCompute.xbar`: the reduced `x`-coordinate `(x : ZMod p)` as a plain field element.
* `ECCompute.num_eq_xbar_mul_den`: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` when `p ∤ x.den`.
* `ECCompute.ydenom_ne_zero`: the `y`-denominator survives reduction when the `x`-denominator does.
-/

open WeierstrassCurve

namespace ECCompute

/-! ### Reducing `x` to `ZMod p`

For `P = (x, y)` on `E` with `p ∤ x.den`, write `X := (x : ZMod p)` (the rational cast) and
`w` with `x.den = w²`. Then `α = x.num - θ·x.den = w²·(X - θ)`. -/

/-- The reduced `x`-coordinate `(x : ZMod p)` of an affine point, as a plain field element. -/
public noncomputable def xbar (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p := (x : ZMod p)

variable {p : ℕ}

/-- Cast identity: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` for a `p`-integral rational. -/
public theorem num_eq_xbar_mul_den [Fact p.Prime] {x : ℚ} (hd : Rat.IsPIntegral p x) :
    (x.num : ZMod p) = xbar p x * (x.den : ZMod p) := by
  rw [xbar, Rat.cast_def, div_mul_cancel₀ _ (Rat.mem_padicInteger_iff.mp hd)]

/-! ### Elementary reduction mod `p`

For a `p`-integral `x` the `y`-coordinate is `p`-integral too, from `x.den = w²`, `y.den = w³`. -/

/-- The `y`-coordinate is `p`-integral whenever the `x`-coordinate is (since
`x.den = w²`, `y.den = w³`). -/
public theorem ydenom_pIntegral {a₂ a₄ a₆ : ℤ} [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hdx : Rat.IsPIntegral p x) :
    Rat.IsPIntegral p y := by
  rw [Rat.mem_padicInteger_iff] at hdx ⊢
  obtain ⟨w, hxw, hyw⟩ := den_isSquare a₂ a₄ a₆ h
  have hw : (w : ZMod p) ≠ 0 := mt (Rat.den_cast_eq_zero_iff two_ne_zero hxw).mpr hdx
  rw [hyw]
  grind

end ECCompute
