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
is defined. A general integral Weierstrass curve `ModelIso.toCurveQ a₁ a₂ a₃ a₄ a₆`
(`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`) must be carried to it. `ModelIso.nonempty_pointAddEquiv`
completes the square but only to a *rational*-coefficient short model; this file adds the integral
scaling step.

The change of variables `⟨u, r, s, t⟩ = ⟨1/2, 0, -a₁/2, -a₃/2⟩` carries `toCurveQ a₁ a₂ a₃ a₄ a₆`
to the integral short model `curve b₂ (8·b₄) (16·b₆)`, with `b`-invariants `b₂ = a₁² + 4a₂`,
`b₄ = 2a₄ + a₁a₃`, `b₆ = a₃² + 4a₆`:

* `A₂ = a₁² + 4a₂`  (`= b₂`),
* `A₄ = 16a₄ + 8a₁a₃`  (`= 8·b₄`),
* `A₆ = 64a₆ + 16a₃²`  (`= 16·b₆`).
-/

namespace ECCompute.ModelChange

open WeierstrassCurve WeierstrassCurve.Affine ModelIso

/-- Two affine points with equal coordinates are equal (nonsingularity proofs are irrelevant). -/
private theorem pointSome_congr {C : WeierstrassCurve ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : C.toAffine.Nonsingular x₁ y₁} {h₂ : C.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : C.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-! ## The scaling isomorphism `(x, y) ↦ (v²x, v³y)`

If two curves have coefficients related by `W'.aᵢ = vⁱ · W.aᵢ`, the map `(x, y) ↦ (v²x, v³y)` is a
group isomorphism.  Each affine-addition ingredient scales by a fixed power of `v`. -/

section Scaling

variable {W W' : WeierstrassCurve ℚ} {v : ℚ}

/-- The defining equation transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem equation_scale (hv : v ≠ 0)
    (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (h3 : W'.a₃ = v ^ 3 * W.a₃)
    (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) (x y : ℚ) :
    W.toAffine.Equation x y ↔ W'.toAffine.Equation (v ^ 2 * x) (v ^ 3 * y) := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff,
    h1, h2, h3, h4, h6]
  constructor
  · intro h; linear_combination v ^ 6 * h
  · intro h; apply mul_left_cancel₀ (pow_ne_zero 6 hv); linear_combination h

/-- Nonsingularity transfers along the scaling `(x, y) ↦ (v²x, v³y)`. -/
theorem nonsingular_scale (hv : v ≠ 0)
    (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (h3 : W'.a₃ = v ^ 3 * W.a₃)
    (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) (x y : ℚ) :
    W.toAffine.Nonsingular x y ↔ W'.toAffine.Nonsingular (v ^ 2 * x) (v ^ 3 * y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.nonsingular_iff']
  refine and_congr (equation_scale hv h1 h2 h3 h4 h6 x y) ?_
  have eX : W'.a₁ * (v ^ 3 * y) - (3 * (v ^ 2 * x) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x) + W'.a₄)
      = v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) := by rw [h1, h2, h4]; ring
  have eY : 2 * (v ^ 3 * y) + W'.a₁ * (v ^ 2 * x) + W'.a₃
      = v ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by rw [h1, h3]; ring
  rw [eX, eY, mul_ne_zero_iff_left (pow_ne_zero 4 hv), mul_ne_zero_iff_left (pow_ne_zero 3 hv)]

/-- Nonsingularity transfers along the inverse scaling `(X, Y) ↦ (X/v², Y/v³)`. -/
theorem nonsingular_scale' (hv : v ≠ 0)
    (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (h3 : W'.a₃ = v ^ 3 * W.a₃)
    (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) (X Y : ℚ) :
    W'.toAffine.Nonsingular X Y ↔ W.toAffine.Nonsingular (X / v ^ 2) (Y / v ^ 3) := by
  rw [nonsingular_scale hv h1 h2 h3 h4 h6 (X / v ^ 2) (Y / v ^ 3),
    mul_div_cancel₀ X (pow_ne_zero 2 hv), mul_div_cancel₀ Y (pow_ne_zero 3 hv)]

/-- The `Y`-negation scales by `v³`. -/
theorem negY_scale (h1 : W'.a₁ = v * W.a₁) (h3 : W'.a₃ = v ^ 3 * W.a₃) (x y : ℚ) :
    W'.toAffine.negY (v ^ 2 * x) (v ^ 3 * y) = v ^ 3 * W.toAffine.negY x y := by
  simp only [WeierstrassCurve.Affine.negY, h1, h3]; ring

/-- The `X`-coordinate of the sum scales by `v²` (the slope scales by `v`). -/
theorem addX_scale (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (x₁ x₂ ℓ : ℚ) :
    W'.toAffine.addX (v ^ 2 * x₁) (v ^ 2 * x₂) (v * ℓ) = v ^ 2 * W.toAffine.addX x₁ x₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, h1, h2]; ring

/-- The intermediate `Y`-coordinate scales by `v³`. -/
theorem negAddY_scale (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (x₁ x₂ y₁ ℓ : ℚ) :
    W'.toAffine.negAddY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.negAddY x₁ x₂ y₁ ℓ := by
  simp only [WeierstrassCurve.Affine.negAddY, addX_scale h1 h2]; ring

/-- The `Y`-coordinate of the sum scales by `v³`. -/
theorem addY_scale (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (h3 : W'.a₃ = v ^ 3 * W.a₃)
    (x₁ x₂ y₁ ℓ : ℚ) :
    W'.toAffine.addY (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v * ℓ)
      = v ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ := by
  rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addY, addX_scale h1 h2,
    negAddY_scale h1 h2, negY_scale h1 h3]

/-- The slope scales by `v`. -/
theorem slope_scale (hv : v ≠ 0)
    (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂) (h3 : W'.a₃ = v ^ 3 * W.a₃)
    (h4 : W'.a₄ = v ^ 4 * W.a₄) (x₁ x₂ y₁ y₂ : ℚ) :
    W'.toAffine.slope (v ^ 2 * x₁) (v ^ 2 * x₂) (v ^ 3 * y₁) (v ^ 3 * y₂)
      = v * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · have hy' : v ^ 3 * y₁ = W'.toAffine.negY (v ^ 2 * x₁) (v ^ 3 * y₂) := by
        rw [negY_scale h1 h3, hy]
      rw [slope_of_Y_eq rfl hy', slope_of_Y_eq rfl hy, mul_zero]
    · have hy' : v ^ 3 * y₁ ≠ W'.toAffine.negY (v ^ 2 * x₁) (v ^ 3 * y₂) := by
        rw [negY_scale h1 h3]
        exact fun hc => hy (mul_left_cancel₀ (pow_ne_zero 3 hv) hc)
      have enum : 3 * (v ^ 2 * x₁) ^ 2 + 2 * W'.a₂ * (v ^ 2 * x₁) + W'.a₄ - W'.a₁ * (v ^ 3 * y₁)
          = v ^ 3 * (v * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)) := by
        rw [h1, h2, h4]; ring
      have eden : v ^ 3 * y₁ - v ^ 3 * W.toAffine.negY x₁ y₁
          = v ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by ring
      rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, negY_scale h1 h3, enum, eden,
        mul_div_mul_left _ _ (pow_ne_zero 3 hv), mul_div_assoc]
  · have hx' : v ^ 2 * x₁ ≠ v ^ 2 * x₂ := fun hc => hx (mul_left_cancel₀ (pow_ne_zero 2 hv) hc)
    have enum : v ^ 3 * y₁ - v ^ 3 * y₂ = v ^ 2 * (v * (y₁ - y₂)) := by ring
    have eden : v ^ 2 * x₁ - v ^ 2 * x₂ = v ^ 2 * (x₁ - x₂) := by ring
    rw [slope_of_X_ne hx', slope_of_X_ne hx, enum, eden,
      mul_div_mul_left _ _ (pow_ne_zero 2 hv), mul_div_assoc]

/-- The forward coordinate map `(x, y) ↦ (v²x, v³y)` on Mordell-Weil groups. -/
def scaleFwd (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale hv h1 h2 h3 h4 h6 x y).mp h)

/-- The inverse coordinate map `(X, Y) ↦ (X/v², Y/v³)`. -/
def scaleBwd (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some X Y h =>
    .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' hv h1 h2 h3 h4 h6 X Y).mp h)

@[simp] theorem scaleFwd_some (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆)
    (x y : ℚ) (h : W.toAffine.Nonsingular x y) :
    scaleFwd hv h1 h2 h3 h4 h6 (.some x y h)
      = .some (v ^ 2 * x) (v ^ 3 * y) ((nonsingular_scale hv h1 h2 h3 h4 h6 x y).mp h) :=
  rfl

@[simp] theorem scaleBwd_some (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆)
    (X Y : ℚ) (h : W'.toAffine.Nonsingular X Y) :
    scaleBwd hv h1 h2 h3 h4 h6 (.some X Y h)
      = .some (X / v ^ 2) (Y / v ^ 3) ((nonsingular_scale' hv h1 h2 h3 h4 h6 X Y).mp h) :=
  rfl

/-- The scaling forward map is additive. -/
theorem scaleFwd_map_add (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆)
    (P Q : W.toAffine.Point) :
    scaleFwd hv h1 h2 h3 h4 h6 (P + Q)
      = scaleFwd hv h1 h2 h3 h4 h6 P + scaleFwd hv h1 h2 h3 h4 h6 Q := by
  rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hycond : v ^ 3 * y₁ = W'.toAffine.negY (v ^ 2 * x₂) (v ^ 3 * y₂) := by
      rw [negY_scale h1 h3, ← hy]
    rw [Point.add_of_Y_eq hx hy, scaleFwd_some, scaleFwd_some,
      Point.add_of_Y_eq (by rw [hx]) hycond]
    rfl
  · have hxy' : ¬(v ^ 2 * x₁ = v ^ 2 * x₂ ∧
        v ^ 3 * y₁ = W'.toAffine.negY (v ^ 2 * x₂) (v ^ 3 * y₂)) := by
      rintro ⟨hx, hy⟩
      refine hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hv) hx, ?_⟩
      rw [negY_scale h1 h3] at hy
      exact mul_left_cancel₀ (pow_ne_zero 3 hv) hy
    have hℓ := slope_scale hv h1 h2 h3 h4 x₁ x₂ y₁ y₂
    rw [Point.add_some hxy]
    simp only [scaleFwd_some]
    rw [Point.add_some hxy']
    refine pointSome_congr ?_ ?_
    · rw [hℓ, addX_scale h1 h2]
    · rw [hℓ, addY_scale h1 h2 h3]

/-- If `W'.aᵢ = vⁱ · W.aᵢ` for a nonzero `v`, then `(x, y) ↦ (v²x, v³y)` is a group isomorphism
`W.Point ≃+ W'.Point`. -/
def scaleEquiv (hv : v ≠ 0) (h1 : W'.a₁ = v * W.a₁) (h2 : W'.a₂ = v ^ 2 * W.a₂)
    (h3 : W'.a₃ = v ^ 3 * W.a₃) (h4 : W'.a₄ = v ^ 4 * W.a₄) (h6 : W'.a₆ = v ^ 6 * W.a₆) :
    W.toAffine.Point ≃+ W'.toAffine.Point :=
  AddEquiv.mk'
    ⟨scaleFwd hv h1 h2 h3 h4 h6, scaleBwd hv h1 h2 h3 h4 h6,
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [scaleFwd_some, scaleBwd_some]
          exact pointSome_congr (mul_div_cancel_left₀ _ (pow_ne_zero 2 hv))
            (mul_div_cancel_left₀ _ (pow_ne_zero 3 hv)),
      fun P => by
        rcases P with _ | ⟨X, Y, h⟩
        · rfl
        · rw [scaleBwd_some, scaleFwd_some]
          exact pointSome_congr (mul_div_cancel₀ _ (pow_ne_zero 2 hv))
            (mul_div_cancel₀ _ (pow_ne_zero 3 hv))⟩
    (scaleFwd_map_add hv h1 h2 h3 h4 h6)

end Scaling

/-! ## The completing-the-square isomorphism as an `AddEquiv`

`ModelIso` proves only `Nonempty` of the completing-the-square equivalence; we rebuild the actual
`AddEquiv` from its public forward/backward maps and additivity lemma. -/

/-- The completing-the-square group isomorphism `toCurveQ … ≃+ shortModel …`. -/
def generalToShortModelEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point ≃+ (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point :=
  AddEquiv.mk'
    ⟨fwd a₁ a₂ a₃ a₄ a₆, bwd a₁ a₂ a₃ a₄ a₆,
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [fwd_some, bwd_some]; exact pointSome_congr rfl (by ring),
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [bwd_some, fwd_some]; exact pointSome_congr rfl (by ring)⟩
    (fwd_map_add a₁ a₂ a₃ a₄ a₆)

/-! ## The integral short model and the change of variables -/

/-- The `a₂` coefficient of the integral short model: `A₂ = a₁² + 4a₂ = b₂`. -/
def intShortA₂ (a₁ a₂ : ℤ) : ℤ := a₁ ^ 2 + 4 * a₂

/-- The `a₄` coefficient of the integral short model: `A₄ = 16a₄ + 8a₁a₃ = 8·b₄`. -/
def intShortA₄ (a₁ a₃ a₄ : ℤ) : ℤ := 16 * a₄ + 8 * a₁ * a₃

/-- The `a₆` coefficient of the integral short model: `A₆ = 64a₆ + 16a₃² = 16·b₆`. -/
def intShortA₆ (a₃ a₆ : ℤ) : ℤ := 64 * a₆ + 16 * a₃ ^ 2

/-- The integral short model `curve (a₁²+4a₂) (16a₄+8a₁a₃) (64a₆+16a₃²)` associated to the general
integral Weierstrass curve `toCurveQ a₁ a₂ a₃ a₄ a₆`. -/
def intShortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  curve (intShortA₂ a₁ a₂) (intShortA₄ a₁ a₃ a₄) (intShortA₆ a₃ a₆)

/-- The composite change of variables `⟨1/2, 0, -a₁/2, -a₃/2⟩` (complete the square, then scale by
`u = 1/2`) is a group isomorphism from the general model `toCurveQ a₁ a₂ a₃ a₄ a₆` to the integral
short model `intShortModel a₁ a₂ a₃ a₄ a₆`, on which the descent character is stated. -/
def generalToShortEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point ≃+ (intShortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point :=
  (generalToShortModelEquiv a₁ a₂ a₃ a₄ a₆).trans <|
    scaleEquiv (W := shortModel a₁ a₂ a₃ a₄ a₆) (W' := intShortModel a₁ a₂ a₃ a₄ a₆) (v := 2)
      two_ne_zero
      (by simp only [intShortModel, curve, shortModel_a₁, mul_zero])
      (by simp only [intShortModel, curve, intShortA₂, shortModel_a₂]; push_cast; ring)
      (by simp only [intShortModel, curve, shortModel_a₃, mul_zero])
      (by simp only [intShortModel, curve, intShortA₄, shortModel_a₄]; push_cast; ring)
      (by simp only [intShortModel, curve, intShortA₆, shortModel_a₆]; push_cast; ring)

end ECCompute.ModelChange
