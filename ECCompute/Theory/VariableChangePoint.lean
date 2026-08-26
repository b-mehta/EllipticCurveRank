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

* `ECCompute.variableChangePointEquiv`: the change of variables as a group isomorphism.
-/

section

namespace ECCompute

open WeierstrassCurve WeierstrassCurve.Affine

variable {W : WeierstrassCurve ℚ} (C : VariableChange ℚ)

/-- Two affine points with equal coordinates are equal (nonsingularity proofs are irrelevant). -/
public theorem point_some_congr {D : WeierstrassCurve ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : D.toAffine.Nonsingular x₁ y₁} {h₂ : D.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : D.toAffine.Point) = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

/-- Elementary disjunction fact underlying the transfer of the nonsingular condition: the two
partial-derivative non-vanishing conditions are related by the invertible substitution
`(F_X, F_Y) ↦ (F_X - σ F_Y, F_Y)` followed by scaling by a unit. -/
public theorem or_ne_zero_sub_iff {A B σ : ℚ} : (A ≠ 0 ∨ B ≠ 0) ↔ (A - σ * B ≠ 0 ∨ B ≠ 0) := by
  by_cases hB : B = 0 <;> simp [hB]

/-! ### Coordinate maps -/

/-- The new `x`-coordinate on `C • W` of the old point `(x, y)`: `u⁻²(x - r)`. -/
def vcX (x : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 2 * (x - C.r)

/-- The new `y`-coordinate on `C • W` of the old point `(x, y)`: `u⁻³(y - s(x - r) - t)`. -/
def vcY (x y : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The new slope on `C • W` of an old line of slope `ℓ`: `u⁻¹(ℓ - s)`. -/
def vcSlope (ℓ : ℚ) : ℚ := (C.u : ℚ)⁻¹ * (ℓ - C.s)

variable {C}

theorem u_ne : (C.u : ℚ) ≠ 0 := C.u.ne_zero

/-! ### Transfer of the curve conditions -/

/-- A point `(x, y)` lies on `W` iff its image lies on `C • W`. -/
theorem equation_variableChange {x y : ℚ} :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (vcX C x) (vcY C x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  rw [Affine.equation_iff, Affine.equation_iff, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Nonsingularity transfers forward along the change of variables. -/
theorem nonsingular_variableChange {x y : ℚ} :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (vcX C x) (vcY C x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  rw [nonsingular_iff', nonsingular_iff', ← equation_variableChange]
  refine and_congr_right fun _ ↦ ?_
  rw [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
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

theorem negY_variableChange {x y : ℚ} :
    (C • W).toAffine.negY (vcX C x) (vcY C x y) = vcY C x (W.toAffine.negY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem addX_variableChange {x₁ x₂ ℓ : ℚ} :
    (C • W).toAffine.addX (vcX C x₁) (vcX C x₂) (vcSlope C ℓ)
      = vcX C (W.toAffine.addX x₁ x₂ ℓ) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [addX, vcX, vcSlope, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem addY_variableChange {x₁ x₂ y₁ ℓ : ℚ} :
    (C • W).toAffine.addY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcSlope C ℓ)
      = vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [addY, negAddY, addX, negY, vcX, vcY, vcSlope, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem vcX_left_cancel {a b : ℚ} (h : vcX C a = vcX C b) : a = b := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcX] at h
  have := mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero hu)) h
  linarith

theorem vcY_left_cancel {x a b : ℚ} (h : vcY C x a = vcY C x b) : a = b := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcY] at h
  have := mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero hu)) h
  linarith

theorem slope_variableChange {x₁ x₂ y₁ y₂ : ℚ} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂)
      = vcSlope C (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  obtain rfl | hx := eq_or_ne x₁ x₂
  · have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    have hyeq : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyeq
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) := by
      rw [negY_variableChange]; exact fun hc ↦ hy (vcY_left_cancel hc)
    have hd1 : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hd2 : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) ≠ 0 :=
      sub_ne_zero.mpr hy'
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy,
      show vcSlope C
            ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
              / (y₁ - W.toAffine.negY x₁ y₁))
          = ((C.u : ℚ)⁻¹
              * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁)
                - C.s * (y₁ - W.toAffine.negY x₁ y₁))) / (y₁ - W.toAffine.negY x₁ y₁)
        from by rw [vcSlope]; field_simp,
      div_eq_div_iff hd2 hd1]
    simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, Units.val_inv_eq_inv_val]
    ring
  · have hx' : vcX C x₁ ≠ vcX C x₂ := fun hc ↦ hx (vcX_left_cancel hc)
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hd' : vcX C x₁ - vcX C x₂ ≠ 0 := sub_ne_zero.mpr hx'
    rw [slope_of_X_ne hx', slope_of_X_ne hx,
      show vcSlope C ((y₁ - y₂) / (x₁ - x₂))
          = ((C.u : ℚ)⁻¹ * (y₁ - y₂ - C.s * (x₁ - x₂))) / (x₁ - x₂)
        from by rw [vcSlope]; field_simp,
      div_eq_div_iff hd' hd]
    simp only [vcX, vcY]
    ring

/-! ### The inverse coordinate maps and round-trip identities -/

variable (C)

/-- The old `x`-coordinate on `W` of the new point `(X, Y)`: `u²X + r`. -/
def vcXinv (X : ℚ) : ℚ := (C.u : ℚ) ^ 2 * X + C.r

/-- The old `y`-coordinate on `W` of the new point `(X, Y)`: `u³Y + u²sX + t`. -/
def vcYinv (X Y : ℚ) : ℚ := (C.u : ℚ) ^ 3 * Y + (C.u : ℚ) ^ 2 * C.s * X + C.t

variable {C}

theorem vcX_vcXinv {X : ℚ} : vcX C (vcXinv C X) = X := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcX, vcXinv]; field_simp; ring

theorem vcY_vcYinv {X Y : ℚ} : vcY C (vcXinv C X) (vcYinv C X Y) = Y := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcY, vcXinv, vcYinv]; field_simp; ring

theorem vcXinv_vcX {x : ℚ} : vcXinv C (vcX C x) = x := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcXinv, vcX]; field_simp; ring

theorem vcYinv_vcX_vcY {x y : ℚ} : vcYinv C (vcX C x) (vcY C x y) = y := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne
  simp only [vcYinv, vcX, vcY]; field_simp; ring

/-! ### The point maps and the group isomorphism -/

/-- The forward coordinate map `(x, y) ↦ (u⁻²(x - r), u⁻³(y - s(x - r) - t))` on Mordell-Weil
groups. -/
def Cfwd (C : VariableChange ℚ) : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (vcX C x) (vcY C x y) (nonsingular_variableChange.mp h)

/-- The inverse coordinate map `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)`. -/
def Cbwd (C : VariableChange ℚ) : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some X Y h =>
    .some (vcXinv C X) (vcYinv C X Y)
      (nonsingular_variableChange.mpr (by rw [vcX_vcXinv, vcY_vcYinv]; exact h))

@[simp] theorem Cfwd_some {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    Cfwd C (.some x y h) = .some (vcX C x) (vcY C x y) (nonsingular_variableChange.mp h) := rfl

@[simp] theorem Cbwd_some {X Y : ℚ} (h : (C • W).toAffine.Nonsingular X Y) :
    Cbwd C (.some X Y h)
      = .some (vcXinv C X) (vcYinv C X Y)
        (nonsingular_variableChange.mpr (by rw [vcX_vcXinv, vcY_vcYinv]; exact h)) := rfl

/-- The forward map commutes with the affine group law on both models. -/
theorem Cfwd_map_add (P Q : W.toAffine.Point) : Cfwd C (P + Q) = Cfwd C P + Cfwd C Q := by
  rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    rw [Point.add_of_Y_eq hx hy, Cfwd_some, Cfwd_some,
      Point.add_of_Y_eq (show vcX C x₁ = vcX C x₂ by rw [hx])
        (show vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂) by
          rw [negY_variableChange, ← hy, hx])]
    rfl
  · have hxy' : ¬(vcX C x₁ = vcX C x₂ ∧
        vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) := by
      rintro ⟨hX, hY⟩
      have hx : x₁ = x₂ := vcX_left_cancel hX
      subst hx
      rw [negY_variableChange] at hY
      exact hxy ⟨rfl, vcY_left_cancel hY⟩
    have hℓ := slope_variableChange (C := C) hp₁.left hp₂.left hxy
    grind [Point.add_some, Cfwd_some, point_some_congr, addX_variableChange, addY_variableChange]

/-- An admissible change of variables `C` induces a group isomorphism between the Mordell-Weil
groups of `W` and `C • W`. -/
public def variableChangePointEquiv (C : VariableChange ℚ) :
    W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk'
    ⟨Cfwd C, Cbwd C,
      fun P ↦ by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [Cfwd_some, Cbwd_some]; exact point_some_congr vcXinv_vcX vcYinv_vcX_vcY,
      fun P ↦ by
        rcases P with _ | ⟨X, Y, h⟩
        · rfl
        · rw [Cbwd_some, Cfwd_some]; exact point_some_congr vcX_vcXinv vcY_vcYinv⟩
    (Cfwd_map_add (C := C))

end ECCompute

end
