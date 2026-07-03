/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Math.Descent.Reduction.Def
import ECCompute.Math.Descent.ReducedArith
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

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

/-- **The kernel of reduction is closed under the group law.**  If two affine points `P`, `Q`
both reduce to the origin mod `p` (`p ∣ x₁.den` and `p ∣ x₂.den`) but are distinct over `ℚ`, then
their sum also reduces to the origin: the `x`-coordinate `x₃ = addX x₁ x₂ (slope …)` of `P + Q`
again has `p ∣ x₃.den`.

This is the one genuinely `p`-adic corner of `red_p` additivity.  It is proved by an explicit
single-fraction certificate: writing `x_i = A_i / w_i²`, `y_i = B_i / w_i³` (`den_isSquare`) with
`E = w₁`, `G = w₂`, `p ∣ E`, `p ∣ G`, the group law gives the integer identity
`x₃ = (N² − a₆E²G²K²) / (A·C·K²)` where `K = A·G² − C·E²` and `N = A·D·E − B·C·G`.  The secant
intercept `ν = N / (E·G·K)` satisfies `N·(A·D·E + B·C·G) = K·W` with `W ≡ −A²C²` a `p`-unit
(both integer identities follow from the two curve relations), so `v_p(N) < v_p(K)`.  Tracking
`padicValRat` through the fraction yields `padicValRat p x₃ = 2·(v_p N − v_p K) < 0`, i.e.
`p ∣ x₃.den`. -/
private theorem den_addX_both_kernel {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hne : x₁ ≠ x₂) (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_X_ne hne]; field_simp
  have haddX : x₃ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    rw [hx3def]; simp only [WeierstrassCurve.Affine.addX, curve]; ring
  have hcv1 := curve_equation_iff a₂ a₄ a₆ h₁
  have hcv2 := curve_equation_iff a₂ a₄ a₆ h₂
  obtain ⟨w₁, hx1d, hy1d⟩ := den_isSquare a₂ a₄ a₆ h₁
  obtain ⟨w₂, hx2d, hy2d⟩ := den_isSquare a₂ a₄ a₆ h₂
  have hw1ne : w₁ ≠ 0 := by intro h; apply x₁.den_ne_zero; rw [hx1d, h]; norm_num
  have hw2ne : w₂ ≠ 0 := by intro h; apply x₂.den_ne_zero; rw [hx2d, h]; norm_num
  set A : ℤ := x₁.num with hAdef
  set B : ℤ := y₁.num with hBdef
  set C : ℤ := x₂.num with hCdef
  set D : ℤ := y₂.num with hDdef
  set E : ℤ := (w₁ : ℤ) with hEdef
  set G : ℤ := (w₂ : ℤ) with hGdef
  have hEQ : (E : ℚ) ≠ 0 := by rw [hEdef]; exact_mod_cast hw1ne
  have hGQ : (G : ℚ) ≠ 0 := by rw [hGdef]; exact_mod_cast hw2ne
  have hE0 : E ≠ 0 := by rw [hEdef]; exact_mod_cast hw1ne
  have hG0 : G ≠ 0 := by rw [hGdef]; exact_mod_cast hw2ne
  -- coordinates as fractions over the square/cube denominators
  have hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2 := by
    have h1 : ((x₁.num : ℤ) : ℚ) = x₁ * (x₁.den : ℚ) :=
      (div_eq_iff (by exact_mod_cast x₁.den_ne_zero)).mp (Rat.num_div_den x₁)
    rw [hAdef, h1, hx1d, hEdef]; push_cast; ring
  have hB : (B : ℚ) = y₁ * (E : ℚ) ^ 3 := by
    have h1 : ((y₁.num : ℤ) : ℚ) = y₁ * (y₁.den : ℚ) :=
      (div_eq_iff (by exact_mod_cast y₁.den_ne_zero)).mp (Rat.num_div_den y₁)
    rw [hBdef, h1, hy1d, hEdef]; push_cast; ring
  have hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2 := by
    have h1 : ((x₂.num : ℤ) : ℚ) = x₂ * (x₂.den : ℚ) :=
      (div_eq_iff (by exact_mod_cast x₂.den_ne_zero)).mp (Rat.num_div_den x₂)
    rw [hCdef, h1, hx2d, hGdef]; push_cast; ring
  have hD : (D : ℚ) = y₂ * (G : ℚ) ^ 3 := by
    have h1 : ((y₂.num : ℤ) : ℚ) = y₂ * (y₂.den : ℚ) :=
      (div_eq_iff (by exact_mod_cast y₂.den_ne_zero)).mp (Rat.num_div_den y₂)
    rw [hDdef, h1, hy2d, hGdef]; push_cast; ring
  -- integer curve relations
  have hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 := by
    have hq : (B : ℚ) ^ 2 = (A : ℚ) ^ 3 + a₂ * (A : ℚ) ^ 2 * (E : ℚ) ^ 2
        + a₄ * (A : ℚ) * (E : ℚ) ^ 4 + a₆ * (E : ℚ) ^ 6 := by
      rw [hA, hB]; linear_combination (E : ℚ) ^ 6 * hcv1
    exact_mod_cast hq
  have hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6 := by
    have hq : (D : ℚ) ^ 2 = (C : ℚ) ^ 3 + a₂ * (C : ℚ) ^ 2 * (G : ℚ) ^ 2
        + a₄ * (C : ℚ) * (G : ℚ) ^ 4 + a₆ * (G : ℚ) ^ 6 := by
      rw [hC, hD]; linear_combination (G : ℚ) ^ 6 * hcv2
    exact_mod_cast hq
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  set W : ℤ := -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
    + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) with hWdef
  -- the two load-bearing integer identities
  have hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) := by
    rw [haddX, hKdef, hNdef]; push_cast; rw [hA, hB, hC, hD]
    linear_combination
      ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₁ * x₂ * (ℓ * x₁ - ℓ * x₂ + y₁ - y₂))) * hℓ
        + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₂ * (x₁ - x₂))) * hcv1
        + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (-x₁ * (x₁ - x₂))) * hcv2
  have hI2 : N * (A * D * E + B * C * G) = K * W := by
    rw [hNdef, hKdef, hWdef]; linear_combination (-C ^ 2 * G ^ 2) * hCR1 + (A ^ 2 * E ^ 2) * hCR2
  -- divisibility facts
  have hpw1 : p ∣ w₁ := by
    have hd1' : p ∣ x₁.den := (ZMod.natCast_eq_zero_iff _ p).mp hd1
    rw [hx1d] at hd1'; exact hp.dvd_of_dvd_pow hd1'
  have hpw2 : p ∣ w₂ := by
    have hd2' : p ∣ x₂.den := (ZMod.natCast_eq_zero_iff _ p).mp hd2
    rw [hx2d] at hd2'; exact hp.dvd_of_dvd_pow hd2'
  have hpE : (p : ℤ) ∣ E := by rw [hEdef]; exact_mod_cast hpw1
  have hpG : (p : ℤ) ∣ G := by rw [hGdef]; exact_mod_cast hpw2
  have hpA : ¬ (p : ℤ) ∣ A := by
    intro hdvd
    have hcop : IsCoprime (A : ℤ) (E ^ 2) := by
      have hc : IsCoprime (x₁.num) ((x₁.den : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_nat_coprime]; simpa using x₁.reduced
      have he : (E : ℤ) ^ 2 = ((x₁.den : ℕ) : ℤ) := by rw [hEdef, hx1d]; push_cast; ring
      rw [hAdef, he]; exact hc
    exact absurd (Int.isUnit_iff.mp
      (hcop.isUnit_of_dvd' hdvd (hpE.trans (dvd_pow_self E two_ne_zero))))
      (by have := hp.two_le; omega)
  have hpC : ¬ (p : ℤ) ∣ C := by
    intro hdvd
    have hcop : IsCoprime (C : ℤ) (G ^ 2) := by
      have hc : IsCoprime (x₂.num) ((x₂.den : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_nat_coprime]; simpa using x₂.reduced
      have he : (G : ℤ) ^ 2 = ((x₂.den : ℕ) : ℤ) := by rw [hGdef, hx2d]; push_cast; ring
      rw [hCdef, he]; exact hc
    exact absurd (Int.isUnit_iff.mp
      (hcop.isUnit_of_dvd' hdvd (hpG.trans (dvd_pow_self G two_ne_zero))))
      (by have := hp.two_le; omega)
  have hA0 : A ≠ 0 := fun h => hpA (h ▸ dvd_zero _)
  have hC0 : C ≠ 0 := fun h => hpC (h ▸ dvd_zero _)
  have hpS : (p : ℤ) ∣ (A * D * E + B * C * G) :=
    dvd_add (hpE.mul_left (A * D)) (hpG.mul_left (B * C))
  have hpW : ¬ (p : ℤ) ∣ W := by
    intro hdvd
    have hrest : (p : ℤ) ∣ (W + A ^ 2 * C ^ 2) := by
      have heq : W + A ^ 2 * C ^ 2
          = E ^ 2 * G ^ 2 * (a₄ * A * C + a₆ * (A * G ^ 2 + C * E ^ 2)) := by rw [hWdef]; ring
      rw [heq]
      exact ((hpE.trans (dvd_pow_self E two_ne_zero)).mul_right (G ^ 2)).mul_right _
    have hAC : (p : ℤ) ∣ A ^ 2 * C ^ 2 := by
      have := dvd_sub hrest hdvd; simpa using this
    rcases hpZ.dvd_mul.mp hAC with h | h
    · exact hpA (hpZ.dvd_of_dvd_pow h)
    · exact hpC (hpZ.dvd_of_dvd_pow h)
  have hW0 : W ≠ 0 := fun h => hpW (h ▸ dvd_zero _)
  have hK0 : K ≠ 0 := by
    intro h
    apply hne
    have hcast : (A : ℚ) * (G : ℚ) ^ 2 = (C : ℚ) * (E : ℚ) ^ 2 := by
      have h0 : (K : ℚ) = 0 := by rw [h]; simp
      rw [hKdef] at h0; push_cast at h0; linarith
    rw [hA, hC] at hcast
    have hEG : (E : ℚ) ^ 2 * (G : ℚ) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hEQ) (pow_ne_zero _ hGQ)
    have hxx : x₁ * ((E : ℚ) ^ 2 * (G : ℚ) ^ 2) = x₂ * ((E : ℚ) ^ 2 * (G : ℚ) ^ 2) := by
      linear_combination hcast
    exact mul_right_cancel₀ hEG hxx
  have hprodne : N * (A * D * E + B * C * G) ≠ 0 := by rw [hI2]; exact mul_ne_zero hK0 hW0
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hprodne
  have hS0 : A * D * E + B * C * G ≠ 0 := right_ne_zero_of_mul hprodne
  -- monotonicity of `padicValInt` under divisibility
  have hmono : ∀ {a b : ℤ}, a ∣ b → b ≠ 0 → padicValInt p a ≤ padicValInt p b := by
    intro a b hab hb
    rcases eq_or_ne a 0 with rfl | ha
    · simp [padicValInt]
    · simp only [padicValInt]
      have h1 : p ^ padicValNat p a.natAbs ∣ a.natAbs :=
        (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Int.natAbs_ne_zero.mpr ha)).mpr le_rfl
      exact (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (Int.natAbs_ne_zero.mpr hb)).mp
        (h1.trans (Int.natAbs_dvd_natAbs.mpr hab))
  have hSval : 1 ≤ padicValInt p (A * D * E + B * C * G) := by
    simp only [padicValInt]
    exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hS0)
      (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpS))
  -- the crux inequality `v_p(N) < v_p(K)`
  have hcrux : padicValInt p N < padicValInt p K := by
    have e1 := padicValInt.mul (p := p) hN0 hS0
    have e2 := padicValInt.mul (p := p) hK0 hW0
    rw [hI2] at e1; rw [e2] at e1
    have hWv : padicValInt p W = 0 := padicValInt.eq_zero_of_not_dvd hpW
    omega
  have hK2 : padicValInt p (K ^ 2) = 2 * padicValInt p K := by
    rw [pow_two, padicValInt.mul hK0 hK0]; ring
  have hNval2 : padicValInt p (N ^ 2) = 2 * padicValInt p N := by
    rw [pow_two, padicValInt.mul hN0 hN0]; ring
  have hpvA : padicValInt p A = 0 := padicValInt.eq_zero_of_not_dvd hpA
  have hpvC : padicValInt p C = 0 := padicValInt.eq_zero_of_not_dvd hpC
  have hDenval : padicValInt p (A * C * K ^ 2) = 2 * padicValInt p K := by
    rw [padicValInt.mul (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0),
      padicValInt.mul hA0 hC0, hpvA, hpvC, hK2]; omega
  -- valuation of the numerator `N² − a₆E²G²K²`
  have hNumval : padicValRat p ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)
      = (2 * padicValInt p N : ℤ) ∧ (N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) ≠ 0 := by
    rcases eq_or_ne (a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) 0 with h0 | h0
    · rw [h0, sub_zero]
      exact ⟨by rw [padicValRat.of_int, hNval2]; push_cast; ring, pow_ne_zero 2 hN0⟩
    · have hsplit : ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)
          = ((N ^ 2 : ℤ) : ℚ) + (-((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)) := by push_cast; ring
      have hq0 : ((N ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hN0
      have hr0 : (-((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)) ≠ 0 := by
        simpa using (show ((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) ≠ 0 by exact_mod_cast h0)
      have hqv : padicValRat p ((N ^ 2 : ℤ) : ℚ) = (2 * padicValInt p N : ℤ) := by
        rw [padicValRat.of_int, hNval2]; push_cast; ring
      have hrv : padicValRat p (-((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ))
          = (padicValInt p (a₆ * E ^ 2 * G ^ 2 * K ^ 2) : ℤ) := by
        rw [padicValRat.neg, padicValRat.of_int]
      have hlt : padicValRat p ((N ^ 2 : ℤ) : ℚ)
          < padicValRat p (-((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)) := by
        rw [hqv, hrv]
        have hdvdK : (K ^ 2 : ℤ) ∣ (a₆ * E ^ 2 * G ^ 2 * K ^ 2) := ⟨a₆ * E ^ 2 * G ^ 2, by ring⟩
        have hle := hmono hdvdK h0
        rw [hK2] at hle
        have : padicValInt p N < padicValInt p K := hcrux
        omega
      have hqrne : ((N ^ 2 : ℤ) : ℚ) + (-((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ)) ≠ 0 := by
        intro he
        have heq : ((N ^ 2 : ℤ) : ℚ) = ((a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) := by
          linear_combination he
        rw [heq] at hlt
        simp only [padicValRat.neg] at hlt
        exact lt_irrefl _ hlt
      refine ⟨?_, ?_⟩
      · rw [hsplit, padicValRat.add_eq_of_lt hqrne hq0 hr0 hlt, hqv]
      · intro he; apply hqrne; rw [← hsplit]; exact_mod_cast he
  obtain ⟨hNumvalQ, hNum0⟩ := hNumval
  have hDen3Q : ((A * C * K ^ 2 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0))
  have hNum3Q : ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hNum0
  have hx3div : x₃
      = ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) / ((A * C * K ^ 2 : ℤ) : ℚ) := by
    rw [eq_div_iff hDen3Q]; exact hMain
  have hx3val : padicValRat p x₃ = (2 * padicValInt p N : ℤ) - (2 * padicValInt p K : ℤ) := by
    rw [hx3div, padicValRat.div hNum3Q hDen3Q, hNumvalQ, padicValRat.of_int, hDenval]
    push_cast; ring
  have hx3neg : padicValRat p x₃ < 0 := by
    rw [hx3val]
    have : padicValInt p N < padicValInt p K := hcrux
    omega
  -- conclude `p ∣ x₃.den`
  have hden0 : padicValNat p x₃.den ≠ 0 := by
    have h' := hx3neg
    rw [padicValRat_def] at h'
    omega
  have hdvd : p ∣ x₃.den := (dvd_iff_padicValNat_ne_zero x₃.den_ne_zero).mpr hden0
  exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd

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
      -- subgroup); it is closed by `den_addX_both_kernel`, the explicit single-fraction
      -- `padicValRat` certificate that the kernel of reduction is closed under the group law.
      rw [Affine.Point.add_of_X_ne hx12]
      exact red_p_of_den_zero a₂ a₄ a₆ p hΔ _
        (den_addX_both_kernel a₂ a₄ a₆ p h₁.1 h₂.1 hx12 hd1 hd2)
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
