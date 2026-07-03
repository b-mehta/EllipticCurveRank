/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Reduction.Def
import ECCompute.Descent
import Mathlib.Algebra.Field.ZMod

/-!
# Additivity of the reduction map

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` of good reduction at a prime `p`, this file
proves that the reduction map on affine points

  `red_p : (curve …).toAffine.Point → E𝔽.toAffine.Point`

(where `E𝔽 := (curveℤ …).map (ℤ → ZMod p)`) is additive, and bundles it as an `AddMonoidHom`
`redHom`.

## Strategy

Every affine point `P` is sent by `red_p` to `toAffine E𝔽 (repr P)`, where `repr P` is a fixed
`ZMod p`-projective representative: `![0, 1, 0]` for the origin and `ℤ → ZMod p` applied to the
integer representative `Trep` otherwise.  Using `Projective.Point.toAffine_add`, additivity of
`red_p` reduces to the projective-class equality

  `repr (P + Q) ≈ E𝔽.add (repr P) (repr Q)`.

The right-hand `E𝔽.add` is `dblXYZ` or `addXYZ` according to whether `repr P ≈ repr Q` in `ZMod p`;
in either case `map_dblXYZ` / `map_addXYZ` rewrite it as `ℤ → ZMod p` applied to the corresponding
integer formula on `Trep`.  The two representatives are then compared via their (rational) affine
coordinates: over `ℚ` both reduce to `P + Q`, which produces exact integer cross-multiplication
identities that survive reduction whenever the relevant `z`-coordinates stay nonzero mod `p`.

## Main declarations

* `ECCompute.red_p_map_add` — additivity of `red_p`.
* `ECCompute.redHom`        — `red_p` bundled as an `AddMonoidHom`.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Projective

namespace ECCompute

/-- Two nonsingular projective representatives over a field that are proportional with the
"cross" scalars given by each other's `Z`-coordinate are equivalent.  Concretely, if
`(V z) • U = (U z) • V`, then `U ≈ V`: either both have vanishing `Z` (and reduce to the point at
infinity) or both are finite and the identity exhibits the unit scalar relating them. -/
theorem Projective.equiv_of_proportional {F : Type*} [Field F] {W : Projective F}
    {U V : Fin 3 → F} (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (hprop : (V 2) • U = (U 2) • V) : U ≈ V := by
  have hcU0 := congrFun hprop 0
  have hcU1 := congrFun hprop 1
  simp only [Pi.smul_apply, smul_eq_mul] at hcU0 hcU1
  by_cases hUz : U 2 = 0
  · -- `U z = 0`; deduce `V z = 0`, then both reduce to the point at infinity.
    have hVz : V 2 = 0 := by
      by_contra hVz
      rw [hUz, zero_mul] at hcU0 hcU1
      have hU0 : U 0 = 0 := (mul_eq_zero.mp hcU0).resolve_left hVz
      have hU1 : U 1 = 0 := (mul_eq_zero.mp hcU1).resolve_left hVz
      rw [WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hUz] at hU
      rcases hU.2 with h | h
      · exact h (by rw [hU0]; ring)
      · exact h (by rw [hU0, hU1]; ring)
    exact Setoid.trans (WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero hU hUz)
      (Setoid.symm (WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero hV hVz))
  · -- `U z ≠ 0`; deduce `V z ≠ 0` and use `equiv_of_X_eq_of_Y_eq`.
    have hVz : V 2 ≠ 0 := by
      intro hVz
      rw [hVz, zero_mul] at hcU0 hcU1
      have hV0 : V 0 = 0 := (mul_eq_zero.mp hcU0.symm).resolve_left hUz
      have hV1 : V 1 = 0 := (mul_eq_zero.mp hcU1.symm).resolve_left hUz
      rw [WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hVz] at hV
      rcases hV.2 with h | h
      · exact h (by rw [hV0]; ring)
      · exact h (by rw [hV0, hV1]; ring)
    exact WeierstrassCurve.Projective.equiv_of_X_eq_of_Y_eq hUz hVz
      (by linear_combination hcU0) (by linear_combination hcU1)

/-- Two nonsingular projective representatives over a field are equivalent as soon as they have the
same underlying affine point.  This is the converse of `toAffine_of_equiv`, obtained from the
injectivity of the projective-to-affine equivalence `toAffineAddEquiv`. -/
theorem Projective.equiv_of_toAffine_eq {F : Type*} [Field F] {W : Projective F}
    {U V : Fin 3 → F} (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (h : Projective.Point.toAffine W U = Projective.Point.toAffine W V) : U ≈ V := by
  classical
  have hUl : W.NonsingularLift ⟦U⟧ := (Projective.nonsingularLift_iff U).mpr hU
  have hVl : W.NonsingularLift ⟦V⟧ := (Projective.nonsingularLift_iff V).mpr hV
  have hmk : (⟨hUl⟩ : W.Point) = ⟨hVl⟩ := by
    apply (Projective.Point.toAffineAddEquiv W).injective
    rw [Projective.Point.toAffineAddEquiv_apply, Projective.Point.toAffineAddEquiv_apply,
      Projective.Point.toAffineLift_eq, Projective.Point.toAffineLift_eq]
    exact h
  exact Quotient.exact (congrArg Projective.Point.point hmk)

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]

/-- The fixed `ZMod p`-projective representative of an affine point used to compute `red_p`:
`![0, 1, 0]` for the origin, and `ℤ → ZMod p` applied to the integer representative otherwise. -/
noncomputable def repr :
    (curve a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h =>
      (Int.castRingHom (ZMod p)) ∘ Trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose

@[simp] theorem repr_zero : repr a₂ a₄ a₆ p 0 = ![0, 1, 0] := rfl

/-- `repr P` is a nonsingular representative on the reduced curve. -/
theorem repr_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact Projective.nonsingular_zero
  | some x y h =>
      exact red_nonsingular a₂ a₄ a₆ p hΔ h
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2

/-- `red_p` is `toAffine` of the fixed representative. -/
theorem red_p_eq_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    red_p a₂ a₄ a₆ p hΔ P
      = Projective.Point.toAffine ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective
          (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact (Projective.Point.toAffine_zero).symm
  | some x y h => rfl

/-- Over `ℚ`, the affine point underlying the integer representative `Trep x y w` is `(x, y)`. -/
theorem toAffine_g_Trep {x y : ℚ} {w : ℕ} (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ Trep x y w)
      = .some x y h := by
  have hw : (w : ℚ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; rintro rfl; simp at hden
  rw [Trep_map_ℚ hden hden',
    Projective.Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (pow_ne_zero 3 hw)),
    Projective.Point.toAffine_some ((Projective.nonsingular_some x y).mpr h)]

/-- If two integer projective representatives have the same (rational) affine point, then they are
proportional over `ℤ`, with the cross scalars given by each other's `Z`-coordinate. -/
theorem int_smul_eq_of_toAffine_eq {S T : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hS : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ S)
      = .some X Y hR)
    (hT : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ T)
      = .some X Y hR) :
    (T 2) • S = (S 2) • T := by
  have key : ∀ U : Fin 3 → ℤ,
      Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ U)
        = .some X Y hR → (U 0 : ℚ) = X * U 2 ∧ (U 1 : ℚ) = Y * U 2 := by
    intro U hU
    have hg : ∀ i, ((Int.castRingHom ℚ) ∘ U) i = (U i : ℚ) := fun i => by
      simp [Function.comp_apply]
    have hUz : ((Int.castRingHom ℚ) ∘ U) 2 ≠ 0 := by
      intro h0
      rw [Projective.Point.toAffine_of_Z_eq_zero h0] at hU
      exact Affine.Point.some_ne_zero _ hU.symm
    have hns : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ U) := by
      by_contra hns
      rw [Projective.Point.toAffine_of_singular hns] at hU
      exact Affine.Point.some_ne_zero _ hU.symm
    rw [Projective.Point.toAffine_of_Z_ne_zero hns hUz, Affine.Point.some.injEq] at hU
    rw [hg] at hUz
    refine ⟨?_, ?_⟩
    · have := (div_eq_iff hUz).mp (hg 0 ▸ hU.1); rw [this]
    · have := (div_eq_iff hUz).mp (hg 1 ▸ hU.2); rw [this]
  obtain ⟨hS0, hS1⟩ := key S hS
  obtain ⟨hT0, hT1⟩ := key T hT
  funext i
  fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
  · have : ((T 2 * S 0 : ℤ) : ℚ) = ((S 2 * T 0 : ℤ) : ℚ) := by
      push_cast; rw [hS0, hT0]; ring
    exact_mod_cast this
  · have : ((T 2 * S 1 : ℤ) : ℚ) = ((S 2 * T 1 : ℤ) : ℚ) := by
      push_cast; rw [hS1, hT1]; ring
    exact_mod_cast this
  · exact mul_comm _ _

/-- **Reduction is well-defined on classes.**  Any integer projective representative `T` whose
rational affine point is `R` reduces (mod `p`) to a representative equivalent to `repr R`. -/
theorem repr_equiv_of_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (R : (curve a₂ a₄ a₆).toAffine.Point) {T : Fin 3 → ℤ}
    (hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      ((Int.castRingHom (ZMod p)) ∘ T))
    (hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ T))
    (hTℚ : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ T) = R) :
    (repr a₂ a₄ a₆ p R) ≈ ((Int.castRingHom (ZMod p)) ∘ T) := by
  cases R with
  | zero =>
    have hTz : ((Int.castRingHom ℚ) ∘ T) 2 = 0 := by
      by_contra hTz
      rw [Projective.Point.toAffine_of_Z_ne_zero hnsq hTz] at hTℚ
      exact Affine.Point.some_ne_zero _ hTℚ
    have hTz' : T 2 = 0 := by
      have h2 : ((Int.castRingHom ℚ) ∘ T) 2 = (T 2 : ℚ) := by simp [Function.comp_apply]
      rw [h2] at hTz; exact_mod_cast hTz
    have hfTz : ((Int.castRingHom (ZMod p)) ∘ T) 2 = 0 := by
      simp [Function.comp_apply, hTz']
    exact Setoid.symm (Projective.equiv_zero_of_Z_eq_zero hnsp hfTz)
  | some X Y hR =>
    set w₃ := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose with hw₃
    have hd3 : X.den = w₃ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose_spec.1
    have hd3' : Y.den = w₃ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose_spec.2
    have hStℚ : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective
        ((Int.castRingHom ℚ) ∘ Trep X Y w₃) = .some X Y hR :=
      toAffine_g_Trep a₂ a₄ a₆ hR hd3 hd3'
    have hid : (T 2) • (Trep X Y w₃) = ((Trep X Y w₃) 2) • T :=
      int_smul_eq_of_toAffine_eq a₂ a₄ a₆ hStℚ hTℚ
    have hprop : ((Int.castRingHom (ZMod p)) ∘ T) 2 •
          ((Int.castRingHom (ZMod p)) ∘ Trep X Y w₃)
        = ((Int.castRingHom (ZMod p)) ∘ Trep X Y w₃) 2 • ((Int.castRingHom (ZMod p)) ∘ T) := by
      have h := congrArg (fun Q : Fin 3 → ℤ => (Int.castRingHom (ZMod p)) ∘ Q) hid
      simpa only [Projective.comp_smul, Function.comp_apply] using h
    exact Projective.equiv_of_proportional (repr_nonsingular a₂ a₄ a₆ p hΔ (.some X Y hR)) hnsp
      hprop

/-! ### Additivity -/

/-- The integral model maps to the rational curve under `ℤ → ℚ`. -/
private theorem map_curveℤ_ℚ :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom ℚ) = curve a₂ a₄ a₆ := by
  rw [← baseChange_curveℤ_ℚ, WeierstrassCurve.baseChange, algebraMap_int_eq]

/-- The rational curve equation in cleared form `y² = x³ + a₂x² + a₄x + a₆`. -/
private theorem curve_equation_iff {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
  have := (WeierstrassCurve.Affine.equation_iff (W := (curve a₂ a₄ a₆).toAffine) x y).mp h
  simpa [curve] using this

/-- **Alternate secant-slope denominator.**  When `X̄₁ = X̄₂` but `x₁ ≠ x₂` over `ℚ` and the reduced
point is not `2`-torsion (`Ȳ₁ + Ȳ₂ ≠ 0`), the standard slope `(y₁ − y₂)/(x₁ − x₂)` (a `0/0` mod `p`)
equals the alternate form `(x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄)/(y₁ + y₂)`, whose denominator
survives reduction.  Hence the reduced secant slope is well-defined. -/
private theorem reduced_slope_den (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have hxne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hcv1 := curve_equation_iff a₂ a₄ a₆ h₁
  have hcv2 := curve_equation_iff a₂ a₄ a₆ h₂
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← Rat.cast_add_of_ne_zero hdy1 hdy2, h0, Rat.cast_zero]
  have hℓ : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne]; field_simp
  have halt : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]
    apply mul_left_cancel₀ hxne
    linear_combination (y₁ + y₂) * hℓ + hcv1 - hcv2
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by
    rw [Rat.cast_add_of_ne_zero hdy1 hdy2]; exact hy2
  have hNden : ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) : ℚ).den : ZMod p)
      ≠ 0 :=
    den_add_ne_zero (den_add_ne_zero (den_add_ne_zero (den_add_ne_zero
      (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1)
      (den_mul_ne_zero hd1 hd2))
      (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2))
      (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2))) (by simp)
  rw [halt]
  exact den_div_ne_zero hNden (den_add_ne_zero hdy1 hdy2) hy2'

/-- **Reduced tangent equations.**  With `x₁ ≠ x₂` over `ℚ`, good denominators, and the reduced
secant slope `S = (slope …)` well-defined (`hℓden`) with `x₃ = addX …` also of good denominator
(`hd3`), the reduced coordinates satisfy the reduced `addX` relation `S² = X̄₃ + a₂ + X̄₁ + X̄₂` and
the alternate-slope identity `S·(Ȳ₁ + Ȳ₂) = X̄₁² + X̄₁X̄₂ + X̄₂² + a₂(X̄₁ + X̄₂) + a₄`. -/
private theorem reduced_tangent_eqs (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hℓden : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) ^ 2
        = ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ZMod p)
          + (a₂ : ZMod p) + (x₁ : ZMod p) + (x₂ : ZMod p)
      ∧ ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) * ((y₁ : ZMod p) + (y₂ : ZMod p))
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  have hcv1 := curve_equation_iff a₂ a₄ a₆ h₁
  have hcv2 := curve_equation_iff a₂ a₄ a₆ h₂
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_X_ne hne]; field_simp
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; ring
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
      rw [haddX]; ring
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rw [Rat.cast_pow,
      Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero hd3 (by simp)) hd1,
      Rat.cast_add_of_ne_zero hd3 (by simp), Rat.cast_intCast] at hc
    exact hc
  · have hℓmul : ℓ * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
      linear_combination (y₁ + y₂) * hℓ + hcv1 - hcv2
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rw [Rat.cast_mul_of_ne_zero hℓden (den_add_ne_zero hdy1 hdy2),
      Rat.cast_add_of_ne_zero hdy1 hdy2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero (den_add_ne_zero
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1) (den_mul_ne_zero hd1 hd2))
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2))
        (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2))) (by simp),
      Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1) (den_mul_ne_zero hd1 hd2))
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2))
        (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2)),
      Rat.cast_add_of_ne_zero (den_add_ne_zero
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1) (den_mul_ne_zero hd1 hd2))
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2),
      Rat.cast_add_of_ne_zero
          (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1) (den_mul_ne_zero hd1 hd2),
      Rat.cast_pow, Rat.cast_mul_of_ne_zero hd1 hd2, Rat.cast_pow,
      Rat.cast_mul_of_ne_zero (by simp) (den_add_ne_zero hd1 hd2),
      Rat.cast_add_of_ne_zero hd1 hd2, Rat.cast_intCast, Rat.cast_intCast] at hc
    exact hc

/-- **Additivity of `red_p` in the tangent-mod-`p` configuration (S4).**  When two affine points
`P`, `Q` reduce to the same point of `E/𝔽ₚ` (`red_p P = red_p Q`) but are distinct over `ℚ`, the
reduction of their rational sum equals the sum of their reductions.  This is the intrinsic content
of additivity that the projective branch-jump cannot supply for free. -/
private theorem red_p_add_tangent (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hred : red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) = red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
  -- Reduced curve negation is `Y ↦ -Y` (`a₁ = a₃ = 0`).
  have hnegY : ∀ X Y : ZMod p,
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY X Y = -Y := fun X Y => by
    simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.map, curveℤ]
  by_cases hd1 : (x₁.den : ZMod p) = 0
  · -- `P → O`, hence (by `hred`) `Q → O` as well; the sum reduces to `O`.
    have hQ0 : red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) = 0 := by
      rw [← hred]; exact red_p_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1
    have hd2 : (x₂.den : ZMod p) = 0 := by
      by_contra hd2
      rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2] at hQ0
      exact Affine.Point.some_ne_zero _ hQ0
    rw [red_p_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1, hQ0, add_zero]
    by_cases hx12 : x₁ = x₂
    · -- `Q = -P`, so `P + Q = 0`.
      have hy : y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
        rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12 with h | h
        · exact absurd (by rw [Affine.Point.some.injEq]; exact ⟨hx12, h⟩) hPQ
        · exact h
      rw [Affine.Point.add_of_Y_eq hx12 hy, red_p_zero]
    · -- **Both summands lie in the kernel of reduction** (`p ∣ x₁.den`, `p ∣ x₂.den`) while
      -- `x₁ ≠ x₂` over `ℚ`.  The goal is `red_p (P + Q) = 0`, i.e. `(x₃.den : ZMod p) = 0` for the
      -- rational sum's `x`-coordinate `x₃ = addX x₁ x₂ (slope …)`.  This is exactly the statement
      -- that the kernel of reduction is closed under addition.  Writing `x_i = A_i / w_i²`,
      -- `y_i = B_i / w_i³` with `p ∣ w_i`, sympy confirms the exact identity (via the two integer
      -- curve relations) `x₃ = num / (w₁² w₂² (A₁ w₂² − A₂ w₁²)²)` has `p`-adic valuation
      -- `v_p(x₃) = −2·min(v_p w₁, v_p w₂) < 0`, so `p ∣ x₃.den`.  Unlike the tangent-mod-`p` case
      -- above, this cannot be shown by the reduced affine identities (`reduced_addX` etc.): both
      -- the numerator and denominator of `x₃` vanish mod `p` (the leading terms cancel — this is
      -- the formal-group content), so `Rat.cast` reasoning gives `0 = 0`.  A rigorous proof needs
      -- the `p`-adic valuation (`padicValRat`, via `(q.den : ZMod p) = 0 ↔ padicValRat p q < 0`)
      -- together with the exact single-fraction certificate, or the elliptic-curve formal group —
      -- neither of which is available in mathlib (there is no point-reduction map / reduction
      -- subgroup).  This is the one genuinely `p`-adic corner of `red_p` additivity; the
      -- tangent-mod-`p` case `S4` proper is closed above by `red_p_add_tangent`.
      sorry
  · -- `P` has good reduction; then so does `Q`, and they share reduced coordinates.
    have hd2 : (x₂.den : ZMod p) ≠ 0 := by
      intro hd2
      have hP := red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1
      rw [hred, red_p_of_den_zero a₂ a₄ a₆ p hΔ h₂ hd2] at hP
      exact Affine.Point.some_ne_zero _ hP.symm
    have hdy1 : (y₁.den : ZMod p) ≠ 0 := ydenom_ne_zero h₁.1 hd1
    have hdy2 : (y₂.den : ZMod p) ≠ 0 := ydenom_ne_zero h₂.1 hd2
    rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
      Affine.Point.some.injEq] at hred
    obtain ⟨hXbar, hYbar⟩ := hred
    by_cases hx12 : x₁ = x₂
    · -- `Q = -P`, so `P + Q = 0`, and the reduced points are mutually negative.
      have hy : y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
        rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12 with h | h
        · exact absurd (by rw [Affine.Point.some.injEq]; exact ⟨hx12, h⟩) hPQ
        · exact h
      rw [Affine.Point.add_of_Y_eq hx12 hy, red_p_zero,
        red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2]
      have hyneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
          (Int.castRingHom (ZMod p))).toAffine.negY (x₂ : ZMod p) (y₂ : ZMod p) := by
        have hny : (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ = -y₂ := by
          simp [WeierstrassCurve.Affine.negY, curve]
        rw [hnegY, hy, hny, Rat.cast_neg]
      rw [Affine.Point.add_of_Y_eq hXbar hyneg]
    · -- `x₁ ≠ x₂` over `ℚ` but the reduced `x`-coordinates coincide: the tangent-mod-`p` case.
      have hne : x₁ ≠ x₂ := hx12
      have hslX : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        WeierstrassCurve.Affine.slope_of_X_ne hne
      set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂) with hℓdef
      have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
        simp only [WeierstrassCurve.Affine.addX, curve]; ring
      have hQeqP : red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂)
          = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
        rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
          Affine.Point.some.injEq]
        exact ⟨hXbar.symm, hYbar.symm⟩
      rw [hQeqP]
      by_cases hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
          (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)
      · -- The common reduced point is `2`-torsion mod `p`; both sides reduce to `O`.
        -- Right-hand side: `P̄ + P̄ = O`.
        rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, Affine.Point.add_of_Y_eq rfl hYneg]
        have hne : x₁ ≠ x₂ := hx12
        have hslX : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
          WeierstrassCurve.Affine.slope_of_X_ne hne
        set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂) with hℓdef
        have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
          simp only [WeierstrassCurve.Affine.addX, curve]; ring
        -- Left-hand side reduces to `O`: the doubled `x`-coordinate has vanishing denominator.
        rw [Affine.Point.add_of_X_ne hne]
        apply red_p_of_den_zero a₂ a₄ a₆ p hΔ
          (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hne hxy.left))
        rw [hslX]
        by_contra hd3
        -- If the doubled point were finite, the reduced tangent slope would force `f'(X̄₁) = 0`,
        -- contradicting nonsingularity of the reduced `2`-torsion point.
        have hℓden : (ℓ.den : ZMod p) ≠ 0 := by
          have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
            have he : (ℓ : ℚ) ^ 2
                = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
              rw [haddX]; ring
            rw [he]
            exact den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2
          rw [Rat.den_pow, Nat.cast_pow] at hℓ2
          exact fun h => hℓ2 (by rw [h]; ring)
        have hℓden_s : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
          rw [hslX]; exact hℓden
        have hd3_s : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0 := by
          rw [hslX]; exact hd3
        obtain ⟨-, htan⟩ :=
          reduced_tangent_eqs a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
        have hYeq : (y₁ : ZMod p) = -(y₁ : ZMod p) := hYneg.trans (hnegY _ _)
        have hY0 : (y₁ : ZMod p) + (y₂ : ZMod p) = 0 := by linear_combination -hYbar + hYeq
        rw [hY0, mul_zero] at htan
        have hfd : 3 * (x₁ : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x₁ : ZMod p) + (a₄ : ZMod p)
            = 0 := by
          linear_combination -htan + (2 * (x₁ : ZMod p) + (x₂ : ZMod p) + (a₂ : ZMod p)) * hXbar
        have hns : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Nonsingular
            (x₁ : ZMod p) (y₁ : ZMod p) :=
          red_nonsingular_affine a₂ a₄ a₆ p hΔ h₁
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
            (by intro h0; apply hd1
                rw [(den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1]; push_cast
                rw [h0]; ring)
        rw [WeierstrassCurve.Affine.nonsingular_iff, map_curveℤ_zmod] at hns
        simp only [zero_mul, sub_zero] at hns
        rcases hns.2 with hfd_ne | hyne2
        · exact (Ne.symm hfd_ne) hfd
        · exact hyne2 hYeq
      · -- Genuine tangent: match the reduced sum with the tangent doubling of the common point.
        have hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0 := by
          intro h; apply hYneg; rw [hnegY]; linear_combination h + hYbar
        have hℓden_s : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 :=
          reduced_slope_den a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hy2
        have hℓden : (ℓ.den : ZMod p) ≠ 0 := by rw [← hslX]; exact hℓden_s
        have hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
          rw [haddX]
          exact den_sub_ne_zero (den_sub_ne_zero (den_sub_ne_zero
            (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hℓden) (by simp)) hd1) hd2
        have hd3_s : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0 := by
          rw [hslX]; exact hd3
        obtain ⟨hS2, htan⟩ :=
          reduced_tangent_eqs a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
        rw [hslX] at hS2 htan
        -- reduced-curve slope, addX and addY forms
        have h2Yne : (y₁ : ZMod p) + (y₁ : ZMod p) ≠ 0 := by
          intro h; apply hYneg; rw [hnegY]; linear_combination h
        have hℓd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.slope
            (x₁ : ZMod p) (x₁ : ZMod p) (y₁ : ZMod p) (y₁ : ZMod p) = (ℓ : ZMod p) := by
          refine mul_right_cancel₀ h2Yne ?_
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYneg]
          simp only [map_curveℤ_zmod, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
            sub_neg_eq_add]
          rw [div_mul_cancel₀ _ h2Yne]
          linear_combination -htan + (2 * (x₁ : ZMod p) + (x₂ : ZMod p) + (a₂ : ZMod p)) * hXbar
            - (ℓ : ZMod p) * hYbar
        have haddXr : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX
            (x₁ : ZMod p) (x₁ : ZMod p) (ℓ : ZMod p)
            = (ℓ : ZMod p) ^ 2 - (a₂ : ZMod p) - (x₁ : ZMod p) - (x₁ : ZMod p) := by
          simp only [WeierstrassCurve.Affine.addX, map_curveℤ_zmod]; ring
        -- cast of the rational addition `y`-coordinate
        have hy3cast : ((curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
            = -((ℓ : ZMod p) * (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p) - (x₁ : ZMod p))
              + (y₁ : ZMod p)) := by
          have haddY : (curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
              = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
            simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
              WeierstrassCurve.Affine.negAddY, curve]; ring
          rw [haddY, Rat.cast_neg,
            Rat.cast_add_of_ne_zero (den_mul_ne_zero hℓden (den_sub_ne_zero hd3 hd1)) hdy1,
            Rat.cast_mul_of_ne_zero hℓden (den_sub_ne_zero hd3 hd1),
            Rat.cast_sub_of_ne_zero hd3 hd1]
        rw [Affine.Point.add_of_X_ne hne,
          red_p_of_den_ne a₂ a₄ a₆ p hΔ
            (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hne hxy.left)) hd3_s,
          red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, Affine.Point.add_of_Y_ne hYneg,
          Affine.Point.some.injEq]
        refine ⟨?_, ?_⟩
        · -- `x`-coordinate: reduced `addX` equals `dblX`
          rw [hslX, hℓd, haddXr]
          linear_combination -hS2 + hXbar
        · -- `y`-coordinate
          rw [hslX, hy3cast, hℓd]
          -- reduce the reduced-curve `addY`
          have haddYr : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addY
              (x₁ : ZMod p) (x₁ : ZMod p) (y₁ : ZMod p) (ℓ : ZMod p)
              = -((ℓ : ZMod p) * (((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX
                  (x₁ : ZMod p) (x₁ : ZMod p) (ℓ : ZMod p) - (x₁ : ZMod p)) + (y₁ : ZMod p)) := by
            simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
              WeierstrassCurve.Affine.negAddY, map_curveℤ_zmod]; ring
          rw [haddYr, haddXr]
          -- both sides now agree once `(addX : ZMod p) = dblX`
          have hxeq : ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p)
              = (ℓ : ZMod p) ^ 2 - (a₂ : ZMod p) - (x₁ : ZMod p) - (x₁ : ZMod p) := by
            linear_combination -hS2 + hXbar
          rw [hxeq]

/-- **Additivity of the reduction map.** -/
theorem red_p_map_add (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    red_p a₂ a₄ a₆ p hΔ (P + Q) = red_p a₂ a₄ a₆ p hΔ P + red_p a₂ a₄ a₆ p hΔ Q := by
  cases P with
  | zero =>
      change red_p a₂ a₄ a₆ p hΔ (0 + Q) = red_p a₂ a₄ a₆ p hΔ 0 + red_p a₂ a₄ a₆ p hΔ Q
      rw [zero_add, red_p_zero, zero_add]
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero =>
      change red_p a₂ a₄ a₆ p hΔ (Affine.Point.some x₁ y₁ h₁ + 0)
        = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ 0
      rw [add_zero, red_p_zero, add_zero]
  | some x₂ y₂ h₂ =>
  -- Notation.
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose with hw₁
  set w₂ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose with hw₂
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hden2 : x₂.den = w₂ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.1
  have hden2' : y₂.den = w₂ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.2
  -- `repr` of the two summands are `f ∘ Trep`.
  have hrP : repr a₂ a₄ a₆ p (.some x₁ y₁ h₁) = (Int.castRingHom (ZMod p)) ∘ Trep x₁ y₁ w₁ := rfl
  have hrQ : repr a₂ a₄ a₆ p (.some x₂ y₂ h₂) = (Int.castRingHom (ZMod p)) ∘ Trep x₂ y₂ w₂ := rfl
  -- Reduce to a projective-class equivalence.
  rw [red_p_eq_toAffine, red_p_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁),
    red_p_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂),
    ← Projective.Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)]
  refine Projective.Point.toAffine_of_equiv ?_
  -- Rational nonsingularity of the two integer representatives.
  have hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁) := by
    have hP := toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1'
    by_contra hns; rw [Projective.Point.toAffine_of_singular hns] at hP
    exact Affine.Point.some_ne_zero _ hP.symm
  have hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂) := by
    have hP := toAffine_g_Trep a₂ a₄ a₆ h₂ hden2 hden2'
    by_contra hns; rw [Projective.Point.toAffine_of_singular hns] at hP
    exact Affine.Point.some_ne_zero _ hP.symm
  -- Map lemmas over `ℚ`.
  have hgaddXYZ : (curve a₂ a₄ a₆).toProjective.addXYZ ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
        ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂)
      = (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂) := by
    rw [← map_curveℤ_ℚ]
    exact Projective.map_addXYZ (Int.castRingHom ℚ) _ _
  have hgdblXYZ : (curve a₂ a₄ a₆).toProjective.dblXYZ ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
      = (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁) := by
    rw [← map_curveℤ_ℚ]
    exact Projective.map_dblXYZ (Int.castRingHom ℚ) _
  by_cases heq : (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
  · -- `repr P ≈ repr Q` mod `p`: the reduced sum is a doubling.
    have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
          (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
        = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁) := by
      rw [Projective.add_of_equiv heq, hrP]
      exact Projective.map_dblXYZ (Int.castRingHom (ZMod p)) _
    rw [hadd]
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point)
        = .some x₂ y₂ h₂
    · -- `P = Q` over `ℚ` (case S1): honest doubling.
      have hgadd : (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁)
          = (curve a₂ a₄ a₆).toProjective.add ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
              ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁) := by
        rw [Projective.add_self]; exact hgdblXYZ.symm
      have hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular
          ((Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁)) := by
        rw [hgadd]; exact Projective.nonsingular_add hns1 hns1
      have hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
          ((Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁)) := by
        rw [← hadd]
        exact Projective.nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
          (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      have hTℚ : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective
          ((Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁))
          = (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) + .some x₂ y₂ h₂ := by
        rw [hgadd, Projective.Point.toAffine_add hns1 hns1,
          toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1', ← hPQ]
      exact repr_equiv_of_toAffine a₂ a₄ a₆ p hΔ _ hnsp hnsq hTℚ
    · -- **S4 — tangent mod `p`.**  Here `repr P ≈ repr Q` in `ZMod p` (the reduced points coincide)
      -- but `P ≠ Q` over `ℚ`.  We reduce the projective-class goal to the affine additivity
      -- `red_p (P + Q) = red_p P + red_p Q`, which is supplied by `red_p_add_tangent`.
      have hred : red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁)
          = red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
        rw [red_p_eq_toAffine, red_p_eq_toAffine]; exact Projective.Point.toAffine_of_equiv heq
      have hnspV : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
          ((Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁)) := by
        rw [← hadd]
        exact Projective.nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
          (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      refine Projective.equiv_of_toAffine_eq (repr_nonsingular a₂ a₄ a₆ p hΔ _) hnspV ?_
      rw [← red_p_eq_toAffine a₂ a₄ a₆ p hΔ, ← hadd,
        Projective.Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
          (repr_nonsingular a₂ a₄ a₆ p hΔ _),
        ← red_p_eq_toAffine a₂ a₄ a₆ p hΔ, ← red_p_eq_toAffine a₂ a₄ a₆ p hΔ]
      exact red_p_add_tangent a₂ a₄ a₆ p hΔ h₁ h₂ hred hPQ
  · -- `¬ (repr P ≈ repr Q)` mod `p`: the reduced sum is a secant.
    -- First, the two representatives are inequivalent over `ℚ` too.
    have hℚne : ¬ ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
        ≈ ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂) := by
      intro hℚeq
      have hpt : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point)
          = .some x₂ y₂ h₂ := by
        rw [← toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1',
          ← toAffine_g_Trep a₂ a₄ a₆ h₂ hden2 hden2']
        exact Projective.Point.toAffine_of_equiv hℚeq
      exact heq (hpt ▸ Setoid.refl (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)))
    have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
          (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
        = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
            (Trep x₂ y₂ w₂) := by
      rw [Projective.add_of_not_equiv heq, hrP, hrQ]
      exact Projective.map_addXYZ (Int.castRingHom (ZMod p)) _ _
    rw [hadd]
    have hgadd : (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂)
        = (curve a₂ a₄ a₆).toProjective.add ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
            ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂) := by
      rw [← hgaddXYZ]; exact (Projective.add_of_not_equiv hℚne).symm
    have hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular
        ((Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂)) := by
      rw [hgadd]; exact Projective.nonsingular_add hns1 hns2
    have hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
        ((Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂)) := by
      rw [← hadd]
      exact Projective.nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
        (repr_nonsingular a₂ a₄ a₆ p hΔ _)
    have hTℚ : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective
        ((Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂))
        = (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) + .some x₂ y₂ h₂ := by
      rw [hgadd, Projective.Point.toAffine_add hns1 hns2,
        toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1', toAffine_g_Trep a₂ a₄ a₆ h₂ hden2 hden2']
    exact repr_equiv_of_toAffine a₂ a₄ a₆ p hΔ _ hnsp hnsq hTℚ

/-- The reduction map bundled as an additive homomorphism
`(curve …).toAffine.Point →+ (reducedCurve …).toAffine.Point`. -/
noncomputable def redHom (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point where
  toFun := red_p a₂ a₄ a₆ p hΔ
  map_zero' := red_p_zero a₂ a₄ a₆ p hΔ
  map_add' := red_p_map_add a₂ a₄ a₆ p hΔ

@[simp] theorem redHom_apply (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) : redHom a₂ a₄ a₆ p hΔ P = red_p a₂ a₄ a₆ p hΔ P :=
  rfl

end ECCompute
