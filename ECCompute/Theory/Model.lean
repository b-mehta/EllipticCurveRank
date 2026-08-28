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
file records the integral model over `ℤ` (`curve a₂ a₄ a₆`) and obtains the rational curve
`curveQ a₂ a₄ a₆` and its reduction `curveZMod a₂ a₄ a₆ p` modulo `p` by base change, along with
`WeierstrassCurve.twoTorsionPoints`, the set of affine points `P` with `P + P = 0`.

## Main declarations

* `ECCompute.curve`: the integral Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℤ`.
* `ECCompute.curveQ`: its base change to `ℚ`; `ECCompute.curveZMod`: its base change modulo `p`.
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

/-- The integral Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℤ`, i.e. `a₁ = a₃ = 0`. -/
@[expose] public def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable {a₂ a₄ a₆ : ℤ}

/-- The rational curve `y² = x³ + a₂x² + a₄x + a₆`, i.e. `curve` base changed to `ℚ`. -/
public abbrev curveQ (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  (curve a₂ a₄ a₆)⁄ℚ

/-- The reduction of the integral model modulo `p`: the base change of `curve` to `ZMod p`. -/
public abbrev curveZMod (a₂ a₄ a₆ : ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  (curve a₂ a₄ a₆)⁄(ZMod p)

/-- `curveQ a₂ a₄ a₆` written as the coefficient tuple `⟨0, a₂, 0, a₄, a₆⟩` over `ℚ`. -/
public theorem curveQ_eq : curveQ a₂ a₄ a₆ = ⟨0, a₂, 0, a₄, a₆⟩ := by
  ext <;> simp [curve, baseChange]

/-- The affine equation of `curveQ a₂ a₄ a₆` in cleared form. -/
@[grind →]
public theorem equation_curve {x y : ℚ} (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by grind [Affine.equation_iff, curveQ_eq]

/-- On the short model `curveQ a₂ a₄ a₆`, the sum's `x`-coordinate is `ℓ² - a₂ - x₁ - x₂`. -/
@[grind =]
public theorem curve_addX {x₁ x₂ ℓ : ℚ} :
    (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  grind [Affine.addX, curveQ_eq]

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the `a₁ = a₃ = 0` case), matching
`WeierstrassCurve.Δ`. -/
@[expose] public def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

/-- The discriminant of `curveQ a₂ a₄ a₆` is the integer `discrInt a₂ a₄ a₆`. -/
public theorem curve_Δ_eq : (curveQ a₂ a₄ a₆).Δ = discrInt a₂ a₄ a₆ := by
  simp only [Δ, b₂, b₄, b₆, b₈, curveQ_eq, discrInt]; grind

/-- The numerator of the discriminant of `curveQ a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
public theorem curve_Δ_num : (curveQ a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  rw [curve_Δ_eq, Rat.num_intCast]

/-- The base change of the integral model to `ℚ` is `curveQ a₂ a₄ a₆`. -/
theorem baseChange_curve_ℚ : (curve a₂ a₄ a₆)⁄ℚ = curveQ a₂ a₄ a₆ := rfl

/-- The integral model maps to `curveQ a₂ a₄ a₆` under `ℤ → ℚ`. -/
public theorem map_curve_ℚ : (curve a₂ a₄ a₆).map (Int.castRingHom ℚ) = curveQ a₂ a₄ a₆ := by
  rw [← baseChange_curve_ℚ, baseChange, algebraMap_int_eq]

variable {p : ℕ}

/-- The reduction of the integral model modulo `p`: the curve with `a₂, a₄, a₆` cast into
`ZMod p`. -/
public theorem curveZMod_eq :
    curveZMod a₂ a₄ a₆ p = ⟨0, a₂, 0, a₄, a₆⟩ := by ext <;> simp [curve, baseChange]

/-- On the reduced curve (where `a₁ = a₃ = 0`) the negation `negY` is `y ↦ -y`. -/
@[grind =]
public theorem reduced_negY {x y : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.negY x y = -y :=
  Affine.negY_of_a₁_a₃_eq_zero _ (by simp [curveZMod_eq]) (by simp [curveZMod_eq])

/-- On the reduced curve, the sum's `x`-coordinate is `ℓ² - a₂ - x₁ - x₂`. -/
@[grind =]
public theorem reduced_addX {x₁ x₂ ℓ : ZMod p} :
    (curveZMod a₂ a₄ a₆ p).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  simp only [Affine.addX, curveZMod_eq]; grind

end ECCompute
