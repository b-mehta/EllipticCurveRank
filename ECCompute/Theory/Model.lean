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

section BaseChange
variable {R : Type*} [CommRing R] [Algebra ℤ R]

/-- The base change of `curve a₂ a₄ a₆` to `R` is the coefficient tuple `⟨0, a₂, 0, a₄, a₆⟩`. -/
public theorem curve_baseChange_eq :
    (curve a₂ a₄ a₆).baseChange R = ⟨0, a₂, 0, a₄, a₆⟩ := by
  ext <;> simp [curve, WeierstrassCurve.baseChange]

/-- On `(curve a₂ a₄ a₆).baseChange R`, the sum's `x`-coordinate is `ℓ² - a₂ - x₁ - x₂`. -/
@[grind =]
public theorem curve_baseChange_addX {x₁ x₂ ℓ : R} :
    ((curve a₂ a₄ a₆).baseChange R).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  simp only [Affine.addX, curve_baseChange_eq]; grind

/-- On `(curve a₂ a₄ a₆).baseChange R` (where `a₁ = a₃ = 0`), the negation `negY` is `y ↦ -y`. -/
@[grind =]
public theorem curve_baseChange_negY {x y : R} :
    ((curve a₂ a₄ a₆).baseChange R).toAffine.negY x y = -y :=
  Affine.negY_of_a₁_a₃_eq_zero _ (by simp [curve_baseChange_eq]) (by simp [curve_baseChange_eq])

end BaseChange

/-- The affine equation of `curveQ a₂ a₄ a₆` in cleared form. -/
@[grind →]
public theorem equation_curveQ {x y : ℚ} (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by grind [Affine.equation_iff, curve_baseChange_eq]

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the `a₁ = a₃ = 0` case), matching
`WeierstrassCurve.Δ`. -/
@[expose] public def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

/-- The numerator of the discriminant of `curveQ a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
public theorem curveQ_Δ_num : (curveQ a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  have : (curveQ a₂ a₄ a₆).Δ = discrInt a₂ a₄ a₆ := by
    simp only [Δ, b₂, b₄, b₆, b₈, curve_baseChange_eq, discrInt]; grind
  rw [this, Rat.num_intCast]

/-- The integral model maps to `curveQ a₂ a₄ a₆` under `ℤ → ℚ`. -/
public theorem map_curve_Q : (curve a₂ a₄ a₆).map (Int.castRingHom ℚ) = curveQ a₂ a₄ a₆ := by
  rw [curveQ, baseChange, algebraMap_int_eq]

end ECCompute
