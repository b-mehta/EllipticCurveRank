/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Reduction.Def
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

/-- **Additivity of the reduction map.**  The only genuinely difficult case is the tangent-mod-`p`
sub-case `S4` (`repr P ≈ repr Q` mod `p` but `P ≠ Q` over `ℚ`), which is left as a documented
`sorry`. -/
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
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point)
        = .some x₂ y₂ h₂
    · -- `P = Q` over `ℚ` (case S1): honest doubling.
      have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
            (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
          = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁) := by
        rw [Projective.add_of_equiv heq, hrP]
        exact Projective.map_dblXYZ (Int.castRingHom (ZMod p)) _
      rw [hadd]
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
    · -- **S4 — tangent mod `p`.**  Here `repr P ≈ repr Q` in `ZMod p` (the reduced points
      -- coincide) but `P ≠ Q` over `ℚ`, so the integer doubling formula `dblXYZ (Trep P)`
      -- represents `2P ≠ P + Q` over `ℚ`; the well-definedness bridge `repr_equiv_of_toAffine`
      -- does not apply and one must instead use the alternate-slope identity
      --   `(y₁ - y₂)(y₁ + y₂) = (x₁ - x₂)(x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄)`
      -- (`dev/reduction-plan.md` §2.4 / `dev/reduction-plan-elementary.md` Chunk D) to identify the
      -- reduced tangent slope `(3X² + 2a₂X + a₄)/(2Ȳ)` and show `repr (P + Q) ≈ dblXYZ (repr P)`.
      -- Remaining goal:
      --   `repr (P + Q) ≈ E𝔽.add (repr P) (repr Q)`   with `repr P ≈ repr Q`, `P ≠ Q`.
      sorry
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
