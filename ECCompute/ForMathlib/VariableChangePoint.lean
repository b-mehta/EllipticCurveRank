/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The Mordell-Weil isomorphism of an admissible change of variables

For an admissible linear change of variables `C = ⟨u, r, s, t⟩` over `ℚ`, the substitution
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` (mathlib's `WeierstrassCurve.VariableChange` action `C • W`)
is a group isomorphism `W.toAffine.Point ≃+ (C • W).toAffine.Point` on Mordell-Weil groups.

## Main results

* `WeierstrassCurve.VariableChange.pointAddEquiv`: the change of variables as a group
  isomorphism.
-/

section

namespace WeierstrassCurve
open Affine

variable {x y x₁ x₂ y₁ y₂ : ℚ}

namespace VariableChange

variable (C : VariableChange ℚ)

/-- The `x`-coordinate on `C • W` of the point with `x`-coordinate `x` on `W`: `u⁻²(x - r)`. -/
def mapX (x : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 2 * (x - C.r)

/-- The `y`-coordinate on `C • W` of the point `(x, y)` on `W`: `u⁻³(y - s(x - r) - t)`. -/
def mapY (x y : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The slope on `C • W` of a line of slope `ℓ` on `W`: `u⁻¹(ℓ - s)`. -/
def mapSlope (ℓ : ℚ) : ℚ := (C.u : ℚ)⁻¹ * (ℓ - C.s)

/-- The `x`-coordinate on `W` of the point with `x`-coordinate `X` on `C • W`: `u²X + r`. -/
def invX (X : ℚ) : ℚ := (C.u : ℚ) ^ 2 * X + C.r

/-- The `y`-coordinate on `W` of the point `(X, Y)` on `C • W`: `u³Y + u²sX + t`. -/
def invY (X Y : ℚ) : ℚ := (C.u : ℚ) ^ 3 * Y + (C.u : ℚ) ^ 2 * C.s * X + C.t

variable {C}

@[local grind .] lemma u_ne_zero : (C.u : ℚ) ≠ 0 := C.u.ne_zero

@[grind =] lemma mapX_invX : C.mapX (C.invX x) = x := by grind [mapX, invX]

@[grind =] lemma mapY_invY : C.mapY (C.invX x) (C.invY x y) = y := by grind [mapY, invX, invY]

@[grind =] lemma invX_mapX : C.invX (C.mapX x) = x := by grind [mapX, invX]

@[grind =] lemma invY_mapY : C.invY (C.mapX x) (C.mapY x y) = y := by grind [mapX, mapY, invY]

@[grind inj] lemma mapX_injective : C.mapX.Injective := by grind [Function.Injective, mapX]

@[grind inj] theorem mapY_injective : (C.mapY x).Injective := by grind [Function.Injective, mapY]

end VariableChange

open VariableChange

variable {W : WeierstrassCurve ℚ} {C : VariableChange ℚ}

/-- A point `(x, y)` lies on `W` iff its image lies on `C • W`. -/
theorem equation_variableChange_iff :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  rw [equation_iff, equation_iff, mapX, mapY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]
  grind [Units.val_inv_eq_inv_val]

/-- Nonsingularity transfers forward along the change of variables. -/
theorem nonsingular_variableChange_iff :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  rw [nonsingular_iff', nonsingular_iff', ← equation_variableChange_iff, mapX, mapY,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  grind [Units.val_inv_eq_inv_val]

/-! ### Transfer of the addition-law ingredients -/

@[grind =]
theorem variableChange_negY :
    (C • W).toAffine.negY (C.mapX x) (C.mapY x y) = C.mapY x (W.toAffine.negY x y) := by
  simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₃]
  grind [Units.val_inv_eq_inv_val]

@[grind =]
theorem variableChange_addX {ℓ : ℚ} :
    (C • W).toAffine.addX (C.mapX x₁) (C.mapX x₂) (C.mapSlope ℓ)
      = C.mapX (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [addX, mapX, mapSlope, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  grind

@[grind =]
theorem variableChange_addY {ℓ : ℚ} :
    (C • W).toAffine.addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapSlope ℓ)
      = C.mapY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, negAddY, addX, negY, mapX, mapY, mapSlope, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  grind

theorem variableChange_slope (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂)
      = C.mapSlope (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  obtain rfl | hx := eq_or_ne x₁ x₂
  · have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hy' : C.mapY x₁ y₁ ≠ (C • W).toAffine.negY (C.mapX x₁) (C.mapY x₁ y₁) := by grind
    have hs : C.mapSlope
          ((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.toAffine.negY x₁ y₁))
        = ((C.u : ℚ)⁻¹
            * ((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)
              - C.s * (y₁ - W.toAffine.negY x₁ y₁))) / (y₁ - W.toAffine.negY x₁ y₁) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, hs, div_eq_div_iff (by grind) (by grind)]
    simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, Units.val_inv_eq_inv_val]
    ring
  · have hs : C.mapSlope ((y₁ - y₂) / (x₁ - x₂))
        = ((C.u : ℚ)⁻¹ * (y₁ - y₂ - C.s * (x₁ - x₂))) / (x₁ - x₂) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_X_ne (by grind), slope_of_X_ne hx, hs, div_eq_div_iff (by grind) (by grind)]
    grind [mapX, mapY]

/-! ### The group isomorphism -/

namespace VariableChange

/-- An admissible change of variables `C` induces a group isomorphism between the Mordell-Weil
groups of `W` and `C • W`, sending `(x, y)` to `(u⁻²(x - r), u⁻³(y - s(x - r) - t))`. -/
public def pointAddEquiv (C : VariableChange ℚ) : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk'
    { toFun := fun
        | .zero => .zero
        | .some x y h => .some (C.mapX x) (C.mapY x y) (nonsingular_variableChange_iff.mp h)
      invFun := fun
        | .zero => .zero
        | .some X Y h => .some (C.invX X) (C.invY X Y)
            (nonsingular_variableChange_iff.mpr (by rwa [mapX_invX, mapY_invY]))
      left_inv := by grind
      right_inv := by grind }
    (by
      rintro P Q
      rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
      any_goals rfl
      simp only [Equiv.coe_fn_mk]
      grind [Point.add_some, variableChange_slope hp₁.1 hp₂.1, Point.zero_def, Point.add_of_Y_eq])

end VariableChange

end WeierstrassCurve

end
