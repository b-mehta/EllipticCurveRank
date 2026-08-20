/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.ForMathlib.WeierstrassCurveAffine
import Mathlib.Data.ZMod.Basic

/-!
# The integral model of the descent curve

The descent character works with the curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ` whose
coefficients are integers. This file records the corresponding curve over `ℤ`,
`curveℤ a₂ a₄ a₆`, together with the structural facts used to build the reduction map and the
shape of negation on the rational and reduced models.

## Main declarations

* `ECCompute.curveℤ`: the integral Weierstrass curve.
* `ECCompute.baseChange_curveℤ_ℚ`: `(curveℤ …).baseChange ℚ = curve …`.
* `ECCompute.map_curveℤ_zmod`: `(curveℤ …).map (Int.castRingHom (ZMod p))` has coefficients
  the images of `a₂, a₄, a₆` in `ZMod p`.
* `ECCompute.negY_curve`, `ECCompute.reduced_negY`: negation is `y ↦ -y` on `curve a₂ a₄ a₆`
  and on its reduction mod `p`.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ)

/-- The integral Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℤ`, i.e. `a₁ = a₃ = 0`. -/
def curveℤ : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

/-- The base change of the integral model to `ℚ` is the original rational curve. -/
theorem baseChange_curveℤ_ℚ : (curveℤ a₂ a₄ a₆).baseChange ℚ = curve a₂ a₄ a₆ := by
  ext <;> simp [WeierstrassCurve.baseChange, curveℤ, curve]

/-- The reduction of the integral model modulo `p`: mapping the coefficients through the ring
homomorphism `ℤ → ZMod p` gives the curve with `a₂, a₄, a₆` cast into `ZMod p`. -/
theorem map_curveℤ_zmod (p : ℕ) :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p)) =
      { a₁ := 0, a₂ := (a₂ : ZMod p), a₃ := 0, a₄ := (a₄ : ZMod p), a₆ := (a₆ : ZMod p) } := by
  ext <;> simp [curveℤ]

/-! ### Negation on the rational and reduced models -/

/-- Negation on the reduced curve is `Y ↦ -Y`, since `a₁ = a₃ = 0` for the integral model. -/
@[grind =]
theorem reduced_negY (p : ℕ) (X Y : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY X Y = -Y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _
    (by simp [map_curveℤ_zmod]) (by simp [map_curveℤ_zmod]) X Y

section RationalNegY

variable {a₂ a₄ a₆}

/-- Negation on `curve a₂ a₄ a₆` is `y ↦ -y`, since `a₁ = a₃ = 0`. -/
theorem negY_curve (x y : ℚ) : (curve a₂ a₄ a₆).toAffine.negY x y = -y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl x y

end RationalNegY

end ECCompute
