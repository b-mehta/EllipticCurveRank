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

open WeierstrassCurve.Affine

namespace WeierstrassCurve

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

theorem u_ne_zero : (C.u : ℚ) ≠ 0 := C.u.ne_zero

theorem mapX_invX {X : ℚ} : C.mapX (C.invX X) = X := by
  simp only [mapX, invX]
  field_simp [u_ne_zero]
  ring

theorem mapY_invY {X Y : ℚ} : C.mapY (C.invX X) (C.invY X Y) = Y := by
  simp only [mapY, invX, invY]
  field_simp [u_ne_zero]
  ring

theorem invX_mapX {x : ℚ} : C.invX (C.mapX x) = x := by
  simp only [invX, mapX]
  field_simp [u_ne_zero]
  ring

theorem invY_mapY {x y : ℚ} : C.invY (C.mapX x) (C.mapY x y) = y := by
  simp only [invY, mapX, mapY]
  field_simp [u_ne_zero]
  ring

theorem mapX_injective : Function.Injective C.mapX := by
  intro a b h
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  simp only [mapX] at h
  have := mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero hu)) h
  linarith

theorem mapY_injective {x : ℚ} : Function.Injective (C.mapY x) := by
  intro a b h
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  simp only [mapY] at h
  have := mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero hu)) h
  linarith

end VariableChange

open VariableChange

variable {W : WeierstrassCurve ℚ} {C : VariableChange ℚ}

/-- Elementary disjunction fact underlying the transfer of the nonsingular condition: the two
partial-derivative non-vanishing conditions are related by the invertible substitution
`(F_X, F_Y) ↦ (F_X - σ F_Y, F_Y)`. -/
private theorem or_ne_zero_sub_iff {A B σ : ℚ} : (A ≠ 0 ∨ B ≠ 0) ↔ (A - σ * B ≠ 0 ∨ B ≠ 0) := by
  by_cases hB : B = 0 <;> simp [hB]

namespace Affine

/-- Two affine points with equal coordinates are equal (nonsingularity proofs are irrelevant). -/
private theorem point_some_congr {D : WeierstrassCurve ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : D.toAffine.Nonsingular x₁ y₁} {h₂ : D.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : D.toAffine.Point) = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

end Affine

/-- A point `(x, y)` lies on `W` iff its image lies on `C • W`. -/
theorem equation_variableChange_iff {x y : ℚ} :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (C.mapX x) (C.mapY x y) := by
  rw [equation_iff, equation_iff, mapX, mapY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  constructor
  · intro h
    field_simp [u_ne_zero]
    linear_combination h
  · intro h
    field_simp [u_ne_zero] at h
    linear_combination h

/-- Nonsingularity transfers forward along the change of variables. -/
theorem nonsingular_variableChange_iff {x y : ℚ} :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  rw [nonsingular_iff', nonsingular_iff', ← equation_variableChange_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [mapX, mapY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  simp only [Units.val_inv_eq_inv_val]
  have eY : (2 * ((C.u : ℚ)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        + (C.u : ℚ)⁻¹ * (W.a₁ + 2 * C.s) * ((C.u : ℚ)⁻¹ ^ 2 * (x - C.r))
        + (C.u : ℚ)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t))
      = (C.u : ℚ)⁻¹ ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by field_simp; ring
  have eX : ((C.u : ℚ)⁻¹ * (W.a₁ + 2 * C.s) * ((C.u : ℚ)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        - (3 * ((C.u : ℚ)⁻¹ ^ 2 * (x - C.r)) ^ 2
          + 2 * ((C.u : ℚ)⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2))
            * ((C.u : ℚ)⁻¹ ^ 2 * (x - C.r))
          + (C.u : ℚ)⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
            + 3 * C.r ^ 2 - 2 * C.s * C.t)))
      = (C.u : ℚ)⁻¹ ^ 4 * ((W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄))
          - (-C.s) * (2 * y + W.a₁ * x + W.a₃)) := by field_simp; ring
  rw [eX, eY, mul_ne_zero_iff_left (pow_ne_zero 4 (inv_ne_zero hu)),
    mul_ne_zero_iff_left (pow_ne_zero 3 (inv_ne_zero hu)), or_ne_zero_sub_iff (σ := -C.s)]

/-! ### Transfer of the addition-law ingredients -/

theorem variableChange_negY {x y : ℚ} :
    (C • W).toAffine.negY (C.mapX x) (C.mapY x y) = C.mapY x (W.toAffine.negY x y) := by
  simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp [u_ne_zero]
  ring

theorem variableChange_addX {x₁ x₂ ℓ : ℚ} :
    (C • W).toAffine.addX (C.mapX x₁) (C.mapX x₂) (C.mapSlope ℓ)
      = C.mapX (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [addX, mapX, mapSlope, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp [u_ne_zero]
  ring

theorem variableChange_addY {x₁ x₂ y₁ ℓ : ℚ} :
    (C • W).toAffine.addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapSlope ℓ)
      = C.mapY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, negAddY, addX, negY, mapX, mapY, mapSlope, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp [u_ne_zero]
  ring

theorem variableChange_slope {x₁ x₂ y₁ y₂ : ℚ} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂)
      = C.mapSlope (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  obtain rfl | hx := eq_or_ne x₁ x₂
  · have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    have hyeq : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyeq
    have hy' : C.mapY x₁ y₁ ≠ (C • W).toAffine.negY (C.mapX x₁) (C.mapY x₁ y₁) := by
      rw [variableChange_negY]; exact fun hc ↦ hy (mapY_injective hc)
    have hd1 : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hd2 : C.mapY x₁ y₁ - (C • W).toAffine.negY (C.mapX x₁) (C.mapY x₁ y₁) ≠ 0 :=
      sub_ne_zero.mpr hy'
    have hs : C.mapSlope
          ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
            / (y₁ - W.toAffine.negY x₁ y₁))
        = ((C.u : ℚ)⁻¹
            * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
              - C.s * (y₁ - W.toAffine.negY x₁ y₁))) / (y₁ - W.toAffine.negY x₁ y₁) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, hs, div_eq_div_iff hd2 hd1]
    simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, Units.val_inv_eq_inv_val]
    ring
  · have hx' : C.mapX x₁ ≠ C.mapX x₂ := fun hc ↦ hx (mapX_injective hc)
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hd' : C.mapX x₁ - C.mapX x₂ ≠ 0 := sub_ne_zero.mpr hx'
    have hs : C.mapSlope ((y₁ - y₂) / (x₁ - x₂))
        = ((C.u : ℚ)⁻¹ * (y₁ - y₂ - C.s * (x₁ - x₂))) / (x₁ - x₂) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_X_ne hx', slope_of_X_ne hx, hs, div_eq_div_iff hd' hd]
    simp only [mapX, mapY]
    ring

/-! ### The group isomorphism -/

namespace VariableChange

/-- An admissible change of variables `C` induces a group isomorphism between the Mordell-Weil
groups of `W` and `C • W`, sending `(x, y)` to `(u⁻²(x - r), u⁻³(y - s(x - r) - t))`. -/
public def pointAddEquiv (C : VariableChange ℚ) : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk'
    { toFun := fun P ↦ match P with
        | .zero => .zero
        | .some x y h => .some (C.mapX x) (C.mapY x y) (nonsingular_variableChange_iff.mp h)
      invFun := fun P ↦ match P with
        | .zero => .zero
        | .some X Y h => .some (C.invX X) (C.invY X Y)
            (nonsingular_variableChange_iff.mpr (by rw [mapX_invX, mapY_invY]; exact h))
      left_inv := fun P ↦ by
        cases P with
        | zero => rfl
        | some x y h => exact Affine.point_some_congr invX_mapX invY_mapY
      right_inv := fun P ↦ by
        cases P with
        | zero => rfl
        | some X Y h => exact Affine.point_some_congr mapX_invX mapY_invY }
    (by
      rintro P Q
      rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
      any_goals rfl
      simp only [Equiv.coe_fn_mk]
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · obtain ⟨hx, hy⟩ := hxy
        have hX : C.mapX x₁ = C.mapX x₂ := by rw [hx]
        have hY : C.mapY x₁ y₁ = (C • W).toAffine.negY (C.mapX x₂) (C.mapY x₂ y₂) := by
          rw [variableChange_negY, ← hy, hx]
        rw [Point.add_of_Y_eq hx hy, Point.add_of_Y_eq hX hY]
        rfl
      · have hxy' : ¬(C.mapX x₁ = C.mapX x₂ ∧
            C.mapY x₁ y₁ = (C • W).toAffine.negY (C.mapX x₂) (C.mapY x₂ y₂)) := by
          rintro ⟨hX, hY⟩
          have hx : x₁ = x₂ := mapX_injective hX
          subst hx
          rw [variableChange_negY] at hY
          exact hxy ⟨rfl, mapY_injective hY⟩
        have hℓ := variableChange_slope (C := C) hp₁.left hp₂.left hxy
        grind [Point.add_some, Affine.point_some_congr, variableChange_addX, variableChange_addY])

end VariableChange

end WeierstrassCurve

end
