/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The short Weierstrass model and its 2-torsion

`ECCompute.curve a₂ a₄ a₆` is the Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ` (the case
`a₁ = a₃ = 0`), the base object the descent argument runs on. `WeierstrassCurve.twoTorsionPoints`
is the set of affine points `P` with `P + P = 0`.
-/

public section

open WeierstrassCurve

namespace WeierstrassCurve

/-- The affine `2`-torsion points of `W`: the points `P` with `P + P = 0`. -/
@[expose] def twoTorsionPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point := {P | P + P = 0}

@[simp]
lemma mem_twoTorsionPoints {W : WeierstrassCurve ℚ} {P : W.toAffine.Point} :
    P ∈ W.twoTorsionPoints ↔ P + P = 0 := Iff.rfl

end WeierstrassCurve

namespace ECCompute

/-- The Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ`, i.e. `a₁ = a₃ = 0`. -/
@[expose] def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable {a₂ a₄ a₆ : ℤ}

/-- The affine equation of `curve a₂ a₄ a₆` in cleared form. -/
@[grind →]
theorem equation_curve {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by grind [Affine.equation_iff, curve]

/-- On the short model `curve a₂ a₄ a₆`, the sum's `x`-coordinate is `ℓ² - a₂ - x₁ - x₂`. -/
theorem curve_addX {x₁ x₂ ℓ : ℚ} :
    (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  simp only [Affine.addX, curve]; grind

end ECCompute
