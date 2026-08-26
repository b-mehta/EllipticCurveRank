/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Defs

import ECCompute.ForMathlib.WeierstrassCurveAffine
import Mathlib.Data.ZMod.Basic

/-!
# The integral model of the descent curve

The descent character works with the curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ` whose
coefficients are integers. This file records the corresponding curve over `ℤ`,
`curveℤ a₂ a₄ a₆`, its reduction `curveZMod a₂ a₄ a₆ p` modulo `p`, and the structural facts
used to build the reduction map.

## Main declarations

* `ECCompute.curveℤ`: the integral Weierstrass curve.
* `ECCompute.curveZMod`: the reduction of `curveℤ` modulo `p`.
* `ECCompute.baseChange_curveℤ_ℚ`: `(curveℤ …).baseChange ℚ = curve …`.
* `ECCompute.map_curveℤ_zmod`: `(curveℤ …).map (Int.castRingHom (ZMod p))` has coefficients
  the images of `a₂, a₄, a₆` in `ZMod p`.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}

/-- The integral Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℤ`, i.e. `a₁ = a₃ = 0`. -/
public def curveℤ (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

/-- The reduction of the integral model `curveℤ` modulo `p`: its base change along `ℤ → ZMod p`. -/
public abbrev curveZMod (a₂ a₄ a₆ : ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  (curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))

/-- The base change of the integral model to `ℚ` is the original rational curve. -/
theorem baseChange_curveℤ_ℚ : (curveℤ a₂ a₄ a₆).baseChange ℚ = curve a₂ a₄ a₆ := by
  ext <;> simp [baseChange, curveℤ, curve]

/-- The integral model maps to the rational curve under `ℤ → ℚ`. -/
public theorem map_curveℤ_ℚ : (curveℤ a₂ a₄ a₆).map (Int.castRingHom ℚ) = curve a₂ a₄ a₆ := by
  rw [← baseChange_curveℤ_ℚ, baseChange, algebraMap_int_eq]

/-- The reduction of the integral model modulo `p`: mapping the coefficients through the ring
homomorphism `ℤ → ZMod p` gives the curve with `a₂, a₄, a₆` cast into `ZMod p`. -/
public theorem map_curveℤ_zmod {p : ℕ} :
    curveZMod a₂ a₄ a₆ p =
      { a₁ := 0, a₂ := (a₂ : ZMod p), a₃ := 0, a₄ := (a₄ : ZMod p), a₆ := (a₆ : ZMod p) } := by
  ext <;> simp [curveℤ]

/-- On the reduced curve (where `a₁ = a₃ = 0`) the negation `negY` is `y ↦ -y`. -/
@[grind =]
public theorem reduced_negY (p : ℕ) (x y : ZMod p) :
    (curveZMod a₂ a₄ a₆ p).toAffine.negY x y = -y :=
  Affine.negY_of_a₁_a₃_eq_zero _ (by simp [map_curveℤ_zmod]) (by simp [map_curveℤ_zmod]) x y

end ECCompute
