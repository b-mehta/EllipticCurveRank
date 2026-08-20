/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.ForMathlib.RatDenom
import ECCompute.ForMathlib.WeierstrassCurveAffine
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
* `ECCompute.negY_curve`: `negY x y = -y` on `curve a₂ a₄ a₆`.
* `ECCompute.ydenom_ne_zero`: the `y`-denominator survives reduction when the `x`-denominator does.
-/

open WeierstrassCurve

namespace ECCompute

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

On `curve a₂ a₄ a₆` (which has `a₁ = a₃ = 0`), `negY x y = -y`, and when `p ∤ x.den` the
`y`-denominator survives reduction, since `x.den = w²` and `y.den = w³`. -/

/-- On `curve a₂ a₄ a₆`, `negY x y = -y` (the curve has `a₁ = a₃ = 0`). -/
theorem negY_curve (x y : ℚ) : (curve a₂ a₄ a₆).toAffine.negY x y = -y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl x y

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
