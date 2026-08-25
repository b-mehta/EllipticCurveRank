/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Reduction.IntModel
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

import ECCompute.Theory.Descent.DenominatorSquare
import ECCompute.ForMathlib.RatDenom

/-!
# The integer projective representative of an affine point

For a point `P = (x, y)` on the rational curve `y² = x³ + a₂x² + a₄x + a₆`, the
denominator-is-a-square lemma gives `w : ℕ` with `x.den = w²` and `y.den = w³`. Then
`![x.num · w, y.num, w³] : Fin 3 → ℤ` is an integer projective representative of `P`, recorded
here as `trep x y w` with the facts used to reduce it modulo `p`.

## Main declarations

* `ECCompute.trep`: the integer representative `![x.num · w, y.num, w³]`.
* `ECCompute.trep_map_ℚ`: over `ℚ`, `trep x y w = w³ • [x : y : 1]`.
* `ECCompute.trep_equation`: `trep x y w` satisfies the projective equation of `curveℤ`.
-/

open WeierstrassCurve Projective

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}

/-- The integer projective representative `![x.num · w, y.num, w³]` of the affine point
`(x, y)`, where `w` is the square-root witness of the denominators (`x.den = w²`, `y.den = w³`).
Over `ℚ` this is `w³ • [x : y : 1]` (see `trep_map_ℚ`). -/
public def trep (x y : ℚ) (w : ℕ) : Fin 3 → ℤ := ![x.num * w, y.num, w ^ 3]

/-- The image of `curveℤ` under `ℤ → ℚ`, in projective form, is the rational curve. -/
theorem map_curveℤ_toProjective :
    (curveℤ a₂ a₄ a₆).toProjective.map (Int.castRingHom ℚ) = (curve a₂ a₄ a₆).toProjective :=
  map_curveℤ_ℚ a₂ a₄ a₆

variable {x y : ℚ} {w : ℕ}

/-- Over `ℚ`, the integer representative equals `w³ • [x : y : 1]`. -/
public theorem trep_map_ℚ (hxden : x.den = w ^ 2) (hyden : y.den = w ^ 3) :
    Int.castRingHom ℚ ∘ trep x y w = (w ^ 3 : ℚ) • ![x, y, 1] := by
  simp [trep, comp_fin3, ← Rat.mul_den_eq_num, hxden, hyden]
  grind

/-- The integer representative lies on the integral projective curve. -/
public theorem trep_equation (h : (curve a₂ a₄ a₆).toAffine.Equation x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curveℤ a₂ a₄ a₆).toProjective.Equation (trep x y w) := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rwa [← map_equation _ (Int.castRingHom ℚ).injective_int, trep_map_ℚ hden hden',
    equation_smul _ (isUnit_iff_ne_zero.2 (by positivity)), equation_some,
    map_curveℤ_toProjective]

end ECCompute
