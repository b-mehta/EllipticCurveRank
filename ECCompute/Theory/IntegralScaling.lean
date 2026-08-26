/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character

import ECCompute.Theory.CompleteSquare

/-!
# The general-to-integer-short-model change of variables

The certified rank bound (`ECCompute.rank_ge_of_certificate`) lives on the integer short model
`curve A₂ A₄ A₆` (`y² = x³ + A₂x² + A₄x + A₆`, `Aᵢ : ℤ`), where the descent character `lambda`
is defined. A general integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`
(`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`) must be carried to it. `CompleteSquare.pointAddEquiv`
completes the square but only to a *rational*-coefficient short model; this file adds the integral
scaling step.

The change of variables `⟨u, r, s, t⟩ = ⟨1/2, 0, -a₁/2, -a₃/2⟩` carries `⟨a₁, a₂, a₃, a₄, a₆⟩`
to the integral short model `curve b₂ (8·b₄) (16·b₆)`, with `b`-invariants `b₂ = a₁² + 4a₂`,
`b₄ = 2a₄ + a₁a₃`, `b₆ = a₃² + 4a₆`:

* `A₂ = a₁² + 4a₂`  (`= b₂`),
* `A₄ = 16a₄ + 8a₁a₃`  (`= 8·b₄`),
* `A₆ = 64a₆ + 16a₃²`  (`= 16·b₆`).

## Main results

* `IntegralScaling.IsScaling`: `W'.aᵢ = vⁱ · W.aᵢ` for a nonzero `v`, the shape of an
  `(x, y) ↦ (v²x, v³y)` rescaling.
* `IntegralScaling.scaleEquiv`: such a scaling is a group isomorphism `W.Point ≃+ W'.Point`.
* `IntegralScaling.intShortModel`: the integral short model of a general integral Weierstrass
  curve over `ℚ`.
* `IntegralScaling.generalToShortEquiv`: the composite `⟨1/2, 0, -a₁/2, -a₃/2⟩` change of
  variables, a group isomorphism from the general model to its integral short model.
-/

namespace ECCompute.IntegralScaling

open WeierstrassCurve WeierstrassCurve.Affine CompleteSquare

/-! ## The scaling isomorphism `(x, y) ↦ (v²x, v³y)`

If two curves have coefficients related by `W'.aᵢ = vⁱ · W.aᵢ`, the map `(x, y) ↦ (v²x, v³y)` is a
group isomorphism. -/

/-- `W'` is the `(x, y) ↦ (v²x, v³y)` rescaling of `W`: `W'.aᵢ = vⁱ · W.aᵢ`, with `v ≠ 0`. -/
structure IsScaling (W W' : WeierstrassCurve ℚ) (v : ℚ) : Prop where
  ne : v ≠ 0
  a₁ : W'.a₁ = v * W.a₁
  a₂ : W'.a₂ = v ^ 2 * W.a₂
  a₃ : W'.a₃ = v ^ 3 * W.a₃
  a₄ : W'.a₄ = v ^ 4 * W.a₄
  a₆ : W'.a₆ = v ^ 6 * W.a₆

section Scaling

variable {W W' : WeierstrassCurve ℚ} {v : ℚ} (s : IsScaling W W' v)
include s

variable {x y X Y x₁ x₂ y₁ ℓ : ℚ}

/-- The defining equation transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem equation_scale :
    W.toAffine.Equation x y ↔ W'.toAffine.Equation (v ^ 2 * x) (v ^ 3 * y) := by
  rw [Affine.equation_iff, Affine.equation_iff, s.a₁, s.a₂, s.a₃, s.a₄, s.a₆]
  exact ⟨fun h ↦ by grind, fun h ↦ mul_left_cancel₀ (pow_ne_zero 6 s.ne) (by grind)⟩

/-- Nonsingularity transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem nonsingular_scale :
    W.toAffine.Nonsingular x y ↔ W'.toAffine.Nonsingular (v ^ 2 * x) (v ^ 3 * y) := by
  rw [nonsingular_iff', nonsingular_iff']
  refine and_congr (equation_scale s) ?_
  have eX : W'.a₁ * (v ^ 3 * y) - (3 * (v ^ 2 * x) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x) + W'.a₄)
      = v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) := by
    grind [IsScaling.a₁, IsScaling.a₂, IsScaling.a₄]
  have eY : 2 * (v ^ 3 * y) + W'.a₁ * (v ^ 2 * x) + W'.a₃
      = v ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by grind [s.a₁, s.a₃]
  rw [eX, eY, mul_ne_zero_iff_left (pow_ne_zero 4 s.ne), mul_ne_zero_iff_left (pow_ne_zero 3 s.ne)]

/-- Nonsingularity transfers along the inverse scaling `(X, Y) ↦ (X/v², Y/v³)`. -/
theorem nonsingular_scale' :
    W'.toAffine.Nonsingular X Y ↔ W.toAffine.Nonsingular (X / v ^ 2) (Y / v ^ 3) := by
  rw [nonsingular_scale s,
    mul_div_cancel₀ X (pow_ne_zero 2 s.ne), mul_div_cancel₀ Y (pow_ne_zero 3 s.ne)]

/-- The `Y`-negation scales by `v³`. -/
theorem negY_scale :
    W'.toAffine.negY (v ^ 2 * x) (v ^ 3 * y) = v ^ 3 * W.toAffine.negY x y := by
  grind [negY, IsScaling.a₁, IsScaling.a₃]

/-- The `X`-coordinate of the sum scales by `v²` (the slope scales by `v`). -/
theorem addX_scale :
    W'.toAffine.addX (v ^ 2 * x₁) (v ^ 2 * x₂) (v * ℓ) = v ^ 2 * W.toAffine.addX x₁ x₂ ℓ := by
  grind [addX, IsScaling.a₁, IsScaling.a₂]

/-- The intermediate `Y`-coordinate scales by `v³`. -/
theorem negAddY_scale :
    W'.toAffine.negAddY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.negAddY x₁ x₂ y₁ ℓ := by grind [negAddY, addX_scale]

/-- The `Y`-coordinate of the sum scales by `v³`. -/
theorem addY_scale :
    W'.toAffine.addY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ := by grind [addY, addX_scale, negAddY_scale, negY_scale]

/-- The slope scales by `v`. -/
theorem slope_scale (x₁ x₂ y₁ y₂ : ℚ) :
    W'.toAffine.slope (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v ^ 3 * y₂)
      = v * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  obtain rfl | hx := eq_or_ne x₁ x₂
  · by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · rw [slope_of_Y_eq rfl (by rw [negY_scale s, hy] : v ^ 3 * y₁ = _),
        slope_of_Y_eq rfl hy, mul_zero]
    · have hy' : v ^ 3 * y₁ ≠ W'.toAffine.negY (v ^ 2 * x₁) (v ^ 3 * y₂) := by
        rw [negY_scale s]
        exact fun hc ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 s.ne) hc)
      have enum : 3 * (v ^ 2 * x₁) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x₁) + W'.a₄ - W'.a₁ * (v ^ 3 * y₁)
          = v ^ 3 * (v * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)) := by
        grind [IsScaling.a₁, IsScaling.a₂, IsScaling.a₄]
      have eden : v ^ 3 * y₁ - v ^ 3 * W.toAffine.negY x₁ y₁
          = v ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by grind
      rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, negY_scale s, enum, eden,
        mul_div_mul_left _ _ (pow_ne_zero 3 s.ne), mul_div_assoc]
  · have hx' : v ^ 2 * x₁ ≠ v ^ 2 * x₂ := fun hc ↦ hx (mul_left_cancel₀ (pow_ne_zero 2 s.ne) hc)
    have enum : v ^ 3 * y₁ - v ^ 3 * y₂ = v ^ 2 * (v * (y₁ - y₂)) := by grind
    have eden : v ^ 2 * x₁ - v ^ 2 * x₂ = v ^ 2 * (x₁ - x₂) := by grind
    rw [slope_of_X_ne hx', slope_of_X_ne hx, enum, eden,
      mul_div_mul_left _ _ (pow_ne_zero 2 s.ne), mul_div_assoc]

/-- The forward coordinate map `(x, y) ↦ (v²x, v³y)` on Mordell-Weil groups. -/
def scaleFwd : W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale s).mp h)

/-- The inverse coordinate map `(X, Y) ↦ (X/v², Y/v³)`. -/
def scaleBwd : W'.toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some X Y h => .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' s).mp h)

@[simp] theorem scaleFwd_some (h : W.toAffine.Nonsingular x y) :
    scaleFwd s (.some x y h) = .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale s).mp h) :=
  rfl

@[simp] theorem scaleBwd_some (h : W'.toAffine.Nonsingular X Y) :
    scaleBwd s (.some X Y h) = .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' s).mp h) :=
  rfl

/-- The scaling forward map is additive. -/
theorem scaleFwd_map_add (P Q : W.toAffine.Point) :
    scaleFwd s (P + Q) = scaleFwd s P + scaleFwd s Q := by
  rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    rw [Point.add_of_Y_eq hx hy, scaleFwd_some, scaleFwd_some,
      Point.add_of_Y_eq (by rw [hx]) (by rw [negY_scale s, ← hy])]
    rfl
  · have hxy' : ¬(v ^ 2 * x₁ = v ^ 2 * x₂ ∧
        v ^ 3 * y₁ = W'.toAffine.negY (v ^ 2 * x₂) (v ^ 3 * y₂)) := by
      rintro ⟨hx, hy⟩
      refine hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 s.ne) hx, ?_⟩
      rw [negY_scale s] at hy
      exact mul_left_cancel₀ (pow_ne_zero 3 s.ne) hy
    have hℓ := slope_scale s x₁ x₂ y₁ y₂
    grind [Point.add_some, scaleFwd_some, point_some_congr, addX_scale, addY_scale]

/-- If `W'.aᵢ = vⁱ · W.aᵢ` for a nonzero `v`, then `(x, y) ↦ (v²x, v³y)` is a group isomorphism
`W.Point ≃+ W'.Point`. -/
def scaleEquiv : W.toAffine.Point ≃+ W'.toAffine.Point :=
  AddEquiv.mk'
    ⟨scaleFwd s, scaleBwd s,
      fun P ↦ by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [scaleFwd_some, scaleBwd_some]
          exact point_some_congr (mul_div_cancel_left₀ _ (pow_ne_zero 2 s.ne))
            (mul_div_cancel_left₀ _ (pow_ne_zero 3 s.ne)),
      fun P ↦ by
        rcases P with _ | ⟨X, Y, h⟩
        · rfl
        · rw [scaleBwd_some, scaleFwd_some]
          exact point_some_congr (mul_div_cancel₀ _ (pow_ne_zero 2 s.ne))
            (mul_div_cancel₀ _ (pow_ne_zero 3 s.ne))⟩
    (scaleFwd_map_add s)

end Scaling

/-! ## The integral short model and the change of variables -/

/-- The `a₂` coefficient of the integral short model: `A₂ = a₁² + 4a₂ = b₂`. -/
@[expose] public def intShortA₂ (a₁ a₂ : ℤ) : ℤ := a₁ ^ 2 + 4 * a₂

/-- The `a₄` coefficient of the integral short model: `A₄ = 16a₄ + 8a₁a₃ = 8·b₄`. -/
@[expose] public def intShortA₄ (a₁ a₃ a₄ : ℤ) : ℤ := 16 * a₄ + 8 * a₁ * a₃

/-- The `a₆` coefficient of the integral short model: `A₆ = 64a₆ + 16a₃² = 16·b₆`. -/
@[expose] public def intShortA₆ (a₃ a₆ : ℤ) : ℤ := 64 * a₆ + 16 * a₃ ^ 2

/-- The integral short model `curve (a₁²+4a₂) (16a₄+8a₁a₃) (64a₆+16a₃²)` associated to the general
integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
@[expose] public def intShortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  curve (a₁ ^ 2 + 4 * a₂) (16 * a₄ + 8 * a₁ * a₃) (64 * a₆ + 16 * a₃ ^ 2)

/-- The composite change of variables `⟨1/2, 0, -a₁/2, -a₃/2⟩` (complete the square, then scale by
`u = 1/2`) is a group isomorphism from the general model `⟨a₁, a₂, a₃, a₄, a₆⟩` to the integral
short model `intShortModel a₁ a₂ a₃ a₄ a₆`, on which the descent character is stated. -/
public def generalToShortEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Point ≃+
      (intShortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point :=
  (pointAddEquiv ⟨a₁, a₂, a₃, a₄, a₆⟩).trans <|
    scaleEquiv
      ⟨two_ne_zero,
        by grind [intShortModel, curve, shortModel_a₁],
        by grind [intShortModel, curve, shortModel_a₂],
        by grind [intShortModel, curve, shortModel_a₃],
        by grind [intShortModel, curve, shortModel_a₄],
        by grind [intShortModel, curve, shortModel_a₆]⟩

end ECCompute.IntegralScaling
