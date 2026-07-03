/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Defs
import Mathlib.Data.ZMod.Basic

/-!
# The integral model of the descent curve

The descent character is built for the curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ` whose
coefficients are genuine integers.  This file records the corresponding curve over `ℤ`,

  `curveℤ a₂ a₄ a₆ : WeierstrassCurve ℤ`,

together with the two structural facts used to build the reduction map: its base change to
`ℚ` is the original curve, and its reduction modulo `p` (mapping the coefficients through
`ℤ → ZMod p`) is the curve with the coefficients cast into `ZMod p`.

## Main declarations

* `ECCompute.curveℤ`            — the integral Weierstrass curve.
* `ECCompute.baseChange_curveℤ_ℚ` — `(curveℤ …).baseChange ℚ = curve …`.
* `ECCompute.map_curveℤ_zmod`   — `(curveℤ …).map (Int.castRingHom (ZMod p))` has coefficients
  the images of `a₂, a₄, a₆` in `ZMod p`.
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
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, curveℤ, curve]

/-- The reduction of the integral model modulo `p`: mapping the coefficients through the ring
homomorphism `ℤ → ZMod p` gives the curve with `a₂, a₄, a₆` cast into `ZMod p`. -/
theorem map_curveℤ_zmod (p : ℕ) :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p)) =
      { a₁ := 0, a₂ := (a₂ : ZMod p), a₃ := 0, a₄ := (a₄ : ZMod p), a₆ := (a₆ : ZMod p) } := by
  ext <;> simp [WeierstrassCurve.map, curveℤ]

end ECCompute
