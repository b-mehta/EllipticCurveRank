/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.ModelIso

/-!
# The general-to-integer-short-model change of variables

The certified rank bound (`ECCompute.rank_ge_of_certificate`) lives on the integer short model
`curve A₂ A₄ A₆` (`y² = x³ + A₂x² + A₄x + A₆`, `Aᵢ : ℤ`), where the descent character `lambda`
is defined. A general integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`
(`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`) must be carried to it. `ModelIso.pointAddEquiv`
completes the square but only to a *rational*-coefficient short model; this file adds the integral
scaling step.

The change of variables `⟨u, r, s, t⟩ = ⟨1/2, 0, -a₁/2, -a₃/2⟩` carries `⟨a₁, a₂, a₃, a₄, a₆⟩`
to the integral short model `curve b₂ (8·b₄) (16·b₆)`, with `b`-invariants `b₂ = a₁² + 4a₂`,
`b₄ = 2a₄ + a₁a₃`, `b₆ = a₃² + 4a₆`:

* `A₂ = a₁² + 4a₂`  (`= b₂`),
* `A₄ = 16a₄ + 8a₁a₃`  (`= 8·b₄`),
* `A₆ = 64a₆ + 16a₃²`  (`= 16·b₆`).
-/

namespace ECCompute.ModelChange

open WeierstrassCurve WeierstrassCurve.Affine ModelIso

/-! ## The scaling isomorphism `(x, y) ↦ (v²x, v³y)`

If two curves have coefficients related by `W'.aᵢ = vⁱ · W.aᵢ`, the map `(x, y) ↦ (v²x, v³y)` is a
group isomorphism.  Each affine-addition ingredient scales by a fixed power of `v`. -/

/-- `W'` is the `(x, y) ↦ (v²x, v³y)` rescaling of `W`: `W'.aᵢ = vⁱ · W.aᵢ`, with `v ≠ 0`. -/
structure IsScaling (W W' : WeierstrassCurve ℚ) (v : ℚ) : Prop where
  ne : v ≠ 0
  a1 : W'.a₁ = v * W.a₁
  a2 : W'.a₂ = v ^ 2 * W.a₂
  a3 : W'.a₃ = v ^ 3 * W.a₃
  a4 : W'.a₄ = v ^ 4 * W.a₄
  a6 : W'.a₆ = v ^ 6 * W.a₆

section Scaling

variable {W W' : WeierstrassCurve ℚ} {v : ℚ} (s : IsScaling W W' v)
include s

/-- The defining equation transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem equation_scale (x y : ℚ) :
    W.toAffine.Equation x y ↔ W'.toAffine.Equation (v ^ 2 * x) (v ^ 3 * y) := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff,
    s.a1, s.a2, s.a3, s.a4, s.a6]
  exact ⟨fun h => by linear_combination v ^ 6 * h,
    fun h => mul_left_cancel₀ (pow_ne_zero 6 s.ne) (by linear_combination h)⟩

/-- Nonsingularity transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem nonsingular_scale (x y : ℚ) :
    W.toAffine.Nonsingular x y ↔ W'.toAffine.Nonsingular (v ^ 2 * x) (v ^ 3 * y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.nonsingular_iff']
  refine and_congr (equation_scale s x y) ?_
  have eX : W'.a₁ * (v ^ 3 * y) - (3 * (v ^ 2 * x) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x) + W'.a₄)
      = v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) := by rw [s.a1, s.a2, s.a4]; ring
  have eY : 2 * (v ^ 3 * y) + W'.a₁ * (v ^ 2 * x) + W'.a₃
      = v ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by rw [s.a1, s.a3]; ring
  rw [eX, eY, mul_ne_zero_iff_left (pow_ne_zero 4 s.ne), mul_ne_zero_iff_left (pow_ne_zero 3 s.ne)]

/-- Nonsingularity transfers along the inverse scaling `(X, Y) ↦ (X/v², Y/v³)`. -/
theorem nonsingular_scale' (X Y : ℚ) :
    W'.toAffine.Nonsingular X Y ↔ W.toAffine.Nonsingular (X / v ^ 2) (Y / v ^ 3) := by
  rw [nonsingular_scale s (X / v ^ 2) (Y / v ^ 3),
    mul_div_cancel₀ X (pow_ne_zero 2 s.ne), mul_div_cancel₀ Y (pow_ne_zero 3 s.ne)]

/-- The `Y`-negation scales by `v³`. -/
theorem negY_scale (x y : ℚ) :
    W'.toAffine.negY (v ^ 2 * x) (v ^ 3 * y) = v ^ 3 * W.toAffine.negY x y := by
  simp only [WeierstrassCurve.Affine.negY, s.a1, s.a3]; ring

/-- The `X`-coordinate of the sum scales by `v²` (the slope scales by `v`). -/
theorem addX_scale (x₁ x₂ ℓ : ℚ) :
    W'.toAffine.addX (v ^ 2 * x₁) (v ^ 2 * x₂) (v * ℓ) = v ^ 2 * W.toAffine.addX x₁ x₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, s.a1, s.a2]; ring

/-- The intermediate `Y`-coordinate scales by `v³`. -/
theorem negAddY_scale (x₁ x₂ y₁ ℓ : ℚ) :
    W'.toAffine.negAddY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.negAddY x₁ x₂ y₁ ℓ := by
  simp only [WeierstrassCurve.Affine.negAddY, addX_scale s]; ring

/-- The `Y`-coordinate of the sum scales by `v³`. -/
theorem addY_scale (x₁ x₂ y₁ ℓ : ℚ) :
    W'.toAffine.addY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ := by
  grind [WeierstrassCurve.Affine.addY, addX_scale, negAddY_scale, negY_scale]

/-- The slope scales by `v`. -/
theorem slope_scale (x₁ x₂ y₁ y₂ : ℚ) :
    W'.toAffine.slope (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v ^ 3 * y₂)
      = v * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · rw [slope_of_Y_eq rfl (by rw [negY_scale s, hy] : v ^ 3 * y₁ = _),
        slope_of_Y_eq rfl hy, mul_zero]
    · have hy' : v ^ 3 * y₁ ≠ W'.toAffine.negY (v ^ 2 * x₁) (v ^ 3 * y₂) := by
        rw [negY_scale s]
        exact fun hc => hy (mul_left_cancel₀ (pow_ne_zero 3 s.ne) hc)
      have enum : 3 * (v ^ 2 * x₁) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x₁) + W'.a₄ - W'.a₁ * (v ^ 3 * y₁)
          = v ^ 3 * (v * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)) := by
        rw [s.a1, s.a2, s.a4]; ring
      have eden : v ^ 3 * y₁ - v ^ 3 * W.toAffine.negY x₁ y₁
          = v ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by ring
      rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, negY_scale s, enum, eden,
        mul_div_mul_left _ _ (pow_ne_zero 3 s.ne), mul_div_assoc]
  · have hx' : v ^ 2 * x₁ ≠ v ^ 2 * x₂ := fun hc => hx (mul_left_cancel₀ (pow_ne_zero 2 s.ne) hc)
    have enum : v ^ 3 * y₁ - v ^ 3 * y₂ = v ^ 2 * (v * (y₁ - y₂)) := by ring
    have eden : v ^ 2 * x₁ - v ^ 2 * x₂ = v ^ 2 * (x₁ - x₂) := by ring
    rw [slope_of_X_ne hx', slope_of_X_ne hx, enum, eden,
      mul_div_mul_left _ _ (pow_ne_zero 2 s.ne), mul_div_assoc]

/-- The forward coordinate map `(x, y) ↦ (v²x, v³y)` on Mordell-Weil groups. -/
def scaleFwd : W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale s x y).mp h)

/-- The inverse coordinate map `(X, Y) ↦ (X/v², Y/v³)`. -/
def scaleBwd : W'.toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some X Y h => .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' s X Y).mp h)

@[simp] theorem scaleFwd_some (x y : ℚ) (h : W.toAffine.Nonsingular x y) :
    scaleFwd s (.some x y h) = .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale s x y).mp h) :=
  rfl

@[simp] theorem scaleBwd_some (X Y : ℚ) (h : W'.toAffine.Nonsingular X Y) :
    scaleBwd s (.some X Y h) = .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' s X Y).mp h) :=
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
    rw [Point.add_some hxy]
    simp only [scaleFwd_some]
    rw [Point.add_some hxy']
    exact point_some_congr (by rw [hℓ, addX_scale s]) (by rw [hℓ, addY_scale s])

/-- If `W'.aᵢ = vⁱ · W.aᵢ` for a nonzero `v`, then `(x, y) ↦ (v²x, v³y)` is a group isomorphism
`W.Point ≃+ W'.Point`. -/
def scaleEquiv : W.toAffine.Point ≃+ W'.toAffine.Point :=
  AddEquiv.mk'
    ⟨scaleFwd s, scaleBwd s,
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [scaleFwd_some, scaleBwd_some]
          exact point_some_congr (mul_div_cancel_left₀ _ (pow_ne_zero 2 s.ne))
            (mul_div_cancel_left₀ _ (pow_ne_zero 3 s.ne)),
      fun P => by
        rcases P with _ | ⟨X, Y, h⟩
        · rfl
        · rw [scaleBwd_some, scaleFwd_some]
          exact point_some_congr (mul_div_cancel₀ _ (pow_ne_zero 2 s.ne))
            (mul_div_cancel₀ _ (pow_ne_zero 3 s.ne))⟩
    (scaleFwd_map_add s)

end Scaling

/-! ## The integral short model and the change of variables -/

/-- The `a₂` coefficient of the integral short model: `A₂ = a₁² + 4a₂ = b₂`. -/
def intShortA₂ (a₁ a₂ : ℤ) : ℤ := a₁ ^ 2 + 4 * a₂

/-- The `a₄` coefficient of the integral short model: `A₄ = 16a₄ + 8a₁a₃ = 8·b₄`. -/
def intShortA₄ (a₁ a₃ a₄ : ℤ) : ℤ := 16 * a₄ + 8 * a₁ * a₃

/-- The `a₆` coefficient of the integral short model: `A₆ = 64a₆ + 16a₃² = 16·b₆`. -/
def intShortA₆ (a₃ a₆ : ℤ) : ℤ := 64 * a₆ + 16 * a₃ ^ 2

/-- The integral short model `curve (a₁²+4a₂) (16a₄+8a₁a₃) (64a₆+16a₃²)` associated to the general
integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
def intShortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  curve (intShortA₂ a₁ a₂) (intShortA₄ a₁ a₃ a₄) (intShortA₆ a₃ a₆)

/-- The general integral Weierstrass curve `⟨a₁, a₂, a₃, a₄, a₆⟩` over `ℚ`. -/
def genModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  ⟨a₁, a₂, a₃, a₄, a₆⟩

private lemma intShortModel_a₂ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (intShortModel a₁ a₂ a₃ a₄ a₆).a₂ = 2 ^ 2 * (shortModel (genModel a₁ a₂ a₃ a₄ a₆)).a₂ := by
  simp only [intShortModel, curve, intShortA₂, shortModel_a₂, genModel]
  push_cast
  ring

private lemma intShortModel_a₄ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (intShortModel a₁ a₂ a₃ a₄ a₆).a₄ = 2 ^ 4 * (shortModel (genModel a₁ a₂ a₃ a₄ a₆)).a₄ := by
  simp only [intShortModel, curve, intShortA₄, shortModel_a₄, genModel]
  push_cast
  ring

private lemma intShortModel_a₆ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (intShortModel a₁ a₂ a₃ a₄ a₆).a₆ = 2 ^ 6 * (shortModel (genModel a₁ a₂ a₃ a₄ a₆)).a₆ := by
  simp only [intShortModel, curve, intShortA₆, shortModel_a₆, genModel]
  push_cast
  ring

/-- The composite change of variables `⟨1/2, 0, -a₁/2, -a₃/2⟩` (complete the square, then scale by
`u = 1/2`) is a group isomorphism from the general model `⟨a₁, a₂, a₃, a₄, a₆⟩` to the integral
short model `intShortModel a₁ a₂ a₃ a₄ a₆`, on which the descent character is stated. -/
def generalToShortEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (genModel a₁ a₂ a₃ a₄ a₆).toAffine.Point ≃+ (intShortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point :=
  (pointAddEquiv (genModel a₁ a₂ a₃ a₄ a₆)).trans <|
    scaleEquiv (W := shortModel (genModel a₁ a₂ a₃ a₄ a₆))
      (W' := intShortModel a₁ a₂ a₃ a₄ a₆) (v := 2)
      ⟨two_ne_zero,
        by simp only [intShortModel, curve, shortModel_a₁, mul_zero],
        intShortModel_a₂ a₁ a₂ a₃ a₄ a₆,
        by simp only [intShortModel, curve, shortModel_a₃, mul_zero],
        intShortModel_a₄ a₁ a₂ a₃ a₄ a₆,
        intShortModel_a₆ a₁ a₂ a₃ a₄ a₆⟩

end ECCompute.ModelChange
