/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import ECCompute.ForMathlib.WeierstrassCurve
import Mathlib.Data.ZMod.Basic

/-!
# The Weierstrass model of the descent curve

The descent argument runs on the curve `y² = x³ + a₂x² + a₄x + a₆` with integer coefficients. This
file records it over `ℚ` (`curve a₂ a₄ a₆`), over `ℤ` (`curveℤ a₂ a₄ a₆`), and its reduction
`curveZMod a₂ a₄ a₆ p` modulo `p`, along with `WeierstrassCurve.twoTorsionPoints`, the set of
affine points `P` with `P + P = 0`.

## Main declarations

* `ECCompute.curve`: the rational Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆`.
* `ECCompute.curveℤ`: its integral model; `ECCompute.curveZMod`: the reduction modulo `p`.
* `WeierstrassCurve.twoTorsionPoints`: the affine `2`-torsion points.
-/

open WeierstrassCurve

namespace WeierstrassCurve

/-- The affine `2`-torsion points of `W`: the points `P` with `P + P = 0`. -/
@[expose] public def twoTorsionPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point :=
  {P | P + P = 0}

@[simp]
public lemma mem_twoTorsionPoints {W : WeierstrassCurve ℚ} {P : W.toAffine.Point} :
    P ∈ W.twoTorsionPoints ↔ P + P = 0 := Iff.rfl

end WeierstrassCurve

namespace ECCompute

/-- The Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ`, i.e. `a₁ = a₃ = 0`. -/
@[expose] public def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable {a₂ a₄ a₆ : ℤ}

/-- The affine equation of `curve a₂ a₄ a₆` in cleared form. -/
@[grind →]
public theorem equation_curve {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by grind [Affine.equation_iff, curve]

/-- On the short model `curve a₂ a₄ a₆`, the sum's `x`-coordinate is `ℓ² - a₂ - x₁ - x₂`. -/
@[grind =]
public theorem curve_addX {x₁ x₂ ℓ : ℚ} :
    (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  simp only [Affine.addX, curve]; grind

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the `a₁ = a₃ = 0` case), matching
`WeierstrassCurve.Δ`. -/
@[expose] public def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

/-- The discriminant of `curve a₂ a₄ a₆` is the integer `discrInt a₂ a₄ a₆`. -/
public theorem curve_Δ_eq : (curve a₂ a₄ a₆).Δ = discrInt a₂ a₄ a₆ := by
  simp only [Δ, b₂, b₄, b₆, b₈, curve, discrInt]; grind

/-- The numerator of the discriminant of `curve a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
public theorem curve_Δ_num : (curve a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  rw [curve_Δ_eq, Rat.num_intCast]

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

variable {p : ℕ}

/-- The reduction of the integral model modulo `p`: mapping the coefficients through the ring
homomorphism `ℤ → ZMod p` gives the curve with `a₂, a₄, a₆` cast into `ZMod p`. -/
public theorem map_curveℤ_zmod :
    curveZMod a₂ a₄ a₆ p =
      { a₁ := 0, a₂ := a₂, a₃ := 0, a₄ := a₄, a₆ := a₆ } := by ext <;> simp [curveℤ]

/-- On the reduced curve (where `a₁ = a₃ = 0`) the negation `negY` is `y ↦ -y`. -/
@[grind =]
public theorem reduced_negY {x y : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.negY x y = -y :=
  Affine.negY_of_a₁_a₃_eq_zero _ (by simp [map_curveℤ_zmod]) (by simp [map_curveℤ_zmod])

end ECCompute
