/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.Def
import ECCompute.Theory.Descent.ReducedArith
import ECCompute.ForMathlib.PadicValInt
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Additivity of the reduction map

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` of good reduction at a prime `p`, this file
proves that the reduction map `red_p` on affine points is additive, and bundles it as an
`AddMonoidHom` `redHom`.

## Main declarations

* `ECCompute.red_p_map_add`: additivity of `red_p`.
* `ECCompute.redHom`: `red_p` bundled as an `AddMonoidHom`.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Projective

namespace ECCompute

open Rat (den_add_ne_zero den_sub_ne_zero den_mul_ne_zero den_pow_ne_zero den_div_ne_zero)

/-- Two nonsingular projective representatives over a field that are proportional with cross
scalars given by each other's `Z`-coordinate are equivalent: if `(V z) • U = (U z) • V`, then
`U ≈ V`. -/
theorem Projective.equiv_of_proportional {F : Type*} [Field F] {W : Projective F}
    {U V : Fin 3 → F} (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (hprop : (V 2) • U = (U 2) • V) : U ≈ V := by
  have hcU0 := congrFun hprop 0
  have hcU1 := congrFun hprop 1
  simp only [Pi.smul_apply, smul_eq_mul] at hcU0 hcU1
  by_cases hUz : U 2 = 0
  · -- `U z = 0`; deduce `V z = 0`, then both reduce to the point at infinity.
    have hVz : V 2 = 0 := by
      rw [WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hUz] at hU
      grind [mul_eq_zero]
    exact Setoid.trans (WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero hU hUz)
      (Setoid.symm (WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero hV hVz))
  · -- `U z ≠ 0`; deduce `V z ≠ 0` and use `equiv_of_X_eq_of_Y_eq`.
    have hVz : V 2 ≠ 0 := fun hVz => by
      rw [WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hVz] at hV
      grind [mul_eq_zero]
    exact WeierstrassCurve.Projective.equiv_of_X_eq_of_Y_eq hUz hVz
      (by grind) (by grind)

/-- Two nonsingular projective representatives over a field are equivalent as soon as they have the
same underlying affine point (the converse of `toAffine_of_equiv`). -/
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
  have hw : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.ne_zero_of_den_eq_pow two_ne_zero hden)
  rw [Trep_map_ℚ hden hden',
    Projective.Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (pow_ne_zero 3 hw)),
    Projective.Point.toAffine_some ((Projective.nonsingular_some x y).mpr h)]

/-- An integer projective representative whose rational affine point is a `some` is nonsingular
over `ℚ` (the affine point of a singular representative is the origin). -/
theorem nonsingular_of_toAffine_some {U : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hU : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ U)
      = .some X Y hR) :
    (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ U) := by
  grind [Projective.Point.toAffine_of_singular, Affine.Point.some_ne_zero]

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
      grind [Projective.Point.toAffine_of_Z_eq_zero, Affine.Point.some_ne_zero]
    have hns : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ U) :=
      nonsingular_of_toAffine_some a₂ a₄ a₆ hU
    rw [Projective.Point.toAffine_of_Z_ne_zero hns hUz, Affine.Point.some.injEq] at hU
    rw [hg] at hUz
    exact ⟨(div_eq_iff hUz).mp (hg 0 ▸ hU.1), (div_eq_iff hUz).mp (hg 1 ▸ hU.2)⟩
  obtain ⟨hS0, hS1⟩ := key S hS
  obtain ⟨hT0, hT1⟩ := key T hT
  funext i
  fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
  · have : ((T 2 * S 0 : ℤ) : ℚ) = ((S 2 * T 0 : ℤ) : ℚ) := by grind
    exact_mod_cast this
  · have : ((T 2 * S 1 : ℤ) : ℚ) = ((S 2 * T 1 : ℤ) : ℚ) := by grind
    exact_mod_cast this
  · exact mul_comm _ _

/-- Reduction is well-defined on classes: any integer projective representative `T` whose
rational affine point is `R` reduces mod `p` to a representative equivalent to `repr R`. -/
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
      grind [Projective.Point.toAffine_of_Z_ne_zero, Affine.Point.some_ne_zero]
    have hTz' : T 2 = 0 := by simpa [Function.comp_apply] using hTz
    have hfTz : ((Int.castRingHom (ZMod p)) ∘ T) 2 = 0 := by simp [Function.comp_apply, hTz']
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

/-- Common closing step for the doubling and secant cases of additivity: an integer
representative `V` whose reduction is the reduced sum (`hadd`) and whose rational value is the
rational sum of two nonsingular representatives `A`, `B` (`hgadd`) is equivalent mod `p` to `repr`
of the affine sum `toAffine A + toAffine B`. -/
theorem sum_repr_equiv (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {V : Fin 3 → ℤ}
    {A B : Fin 3 → ℚ} (P Q : (curve a₂ a₄ a₆).toAffine.Point)
    (hnsA : (curve a₂ a₄ a₆).toProjective.Nonsingular A)
    (hnsB : (curve a₂ a₄ a₆).toProjective.Nonsingular B)
    (hgadd : (Int.castRingHom ℚ) ∘ V = (curve a₂ a₄ a₆).toProjective.add A B)
    (haffA : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective A = P)
    (haffB : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective B = Q)
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
      (repr a₂ a₄ a₆ p P) (repr a₂ a₄ a₆ p Q) = (Int.castRingHom (ZMod p)) ∘ V) :
    repr a₂ a₄ a₆ p (P + Q) ≈ ((Int.castRingHom (ZMod p)) ∘ V) := by
  have hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      ((Int.castRingHom (ZMod p)) ∘ V) := by
    rw [← hadd]
    exact Projective.nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)
  have hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ V) := by
    rw [hgadd]; exact Projective.nonsingular_add hnsA hnsB
  have hTℚ : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ V)
      = P + Q := by rw [hgadd, Projective.Point.toAffine_add hnsA hnsB, haffA, haffB]
  exact repr_equiv_of_toAffine a₂ a₄ a₆ p hΔ _ hnsp hnsq hTℚ

/-! ### Additivity -/

/-- The integral model maps to the rational curve under `ℤ → ℚ`. -/
private theorem map_curveℤ_ℚ :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom ℚ) = curve a₂ a₄ a₆ := by
  rw [← baseChange_curveℤ_ℚ, WeierstrassCurve.baseChange, algebraMap_int_eq]

/-- The rational curve equation in cleared form `y² = x³ + a₂x² + a₄x + a₆`. -/
private theorem curve_equation_iff {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
  grind [WeierstrassCurve.Affine.equation_iff, curve]

/-- The secant numerator `x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄` has good denominator, and its
reduction is the corresponding polynomial in `X̄₁, X̄₂`. -/
private theorem cast_secant_num {x₁ x₂ : ℚ} (hd1 : (x₁.den : ZMod p) ≠ 0)
    (hd2 : (x₂.den : ZMod p) ≠ 0) :
    ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)).den : ZMod p) ≠ 0
      ∧ ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) : ℚ) : ZMod p)
        = (x₁ : ZMod p) ^ 2 + (x₁ : ZMod p) * (x₂ : ZMod p) + (x₂ : ZMod p) ^ 2
          + (a₂ : ZMod p) * ((x₁ : ZMod p) + (x₂ : ZMod p)) + (a₄ : ZMod p) := by
  have hx1sq : ((x₁ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd1
  have hx2sq : ((x₂ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hd2
  have hprod : ((x₁ * x₂ : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero hd1 hd2
  have hd : ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)).den : ZMod p) ≠ 0 :=
    den_add_ne_zero (den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hx1sq hprod) hx2sq)
      (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2))) (by simp)
  refine ⟨hd, ?_⟩
  rw [Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hx1sq hprod) hx2sq)
        (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2))) (by simp),
    Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hx1sq hprod) hx2sq)
      (den_mul_ne_zero (by simp) (den_add_ne_zero hd1 hd2)),
    Rat.cast_add_of_ne_zero (den_add_ne_zero hx1sq hprod) hx2sq,
    Rat.cast_add_of_ne_zero hx1sq hprod, Rat.cast_pow, Rat.cast_mul_of_ne_zero hd1 hd2,
    Rat.cast_pow, Rat.cast_mul_of_ne_zero (by simp) (den_add_ne_zero hd1 hd2),
    Rat.cast_add_of_ne_zero hd1 hd2, Rat.cast_intCast, Rat.cast_intCast]

/-- The reduced secant slope times `y₁ + y₂` equals the secant numerator: clearing the denominator
of `slope = (y₁ - y₂)/(x₁ - x₂)` against the two curve relations gives
`slope·(y₁ + y₂) = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄`. -/
private theorem slope_mul_add_eq (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂) :
    (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂)
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
  have hcv1 := curve_equation_iff a₂ a₄ a₆ h₁
  have hcv2 := curve_equation_iff a₂ a₄ a₆ h₂
  have hℓ : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne]; grind
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
  grind

/-- The reduced secant slope is well-defined. When `X̄₁ = X̄₂` but `x₁ ≠ x₂` over `ℚ` and the
reduced point is not `2`-torsion (`Ȳ₁ + Ȳ₂ ≠ 0`), the standard slope `(y₁ - y₂)/(x₁ - x₂)` (a
`0/0` mod `p`) equals the alternate form `(x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄)/(y₁ + y₂)`, whose
denominator survives reduction. -/
private theorem reduced_slope_den (hne : x₁ ≠ x₂)
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← Rat.cast_add_of_ne_zero hdy1 hdy2, h0, Rat.cast_zero]
  have halt : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ)) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by rwa [Rat.cast_add_of_ne_zero hdy1 hdy2]
  have hNden := (cast_secant_num a₂ a₄ p hd1 hd2).1
  rw [halt]
  exact den_div_ne_zero hNden (den_add_ne_zero hdy1 hdy2) hy2'

/-- The reduced coordinates satisfy the reduced `addX` relation `S² = X̄₃ + a₂ + X̄₁ + X̄₂` and the
alternate-slope identity `S·(Ȳ₁ + Ȳ₂) = X̄₁² + X̄₁X̄₂ + X̄₂² + a₂(X̄₁ + X̄₂) + a₄`, for the reduced
secant slope `S = (slope …)`. -/
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
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
      grind
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rw [Rat.cast_pow,
      Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero hd3 (by simp)) hd1,
      Rat.cast_add_of_ne_zero hd3 (by simp), Rat.cast_intCast] at hc
    exact hc
  · have hℓmul : ℓ * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ : ℚ) * (x₁ + x₂) + (a₄ : ℚ) := by
      rw [hℓdef]; exact slope_mul_add_eq a₂ a₄ a₆ hne h₁ h₂
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rw [Rat.cast_mul_of_ne_zero hℓden (den_add_ne_zero hdy1 hdy2),
      Rat.cast_add_of_ne_zero hdy1 hdy2, (cast_secant_num a₂ a₄ p hd1 hd2).2] at hc
    exact hc

/-- `(q.num : ℚ) = q * wᵏ` when `q.den = wᵏ`, clearing the denominator of a rational. -/
private theorem cast_num_eq {q : ℚ} {w k : ℕ} (hd : q.den = w ^ k) :
    (q.num : ℚ) = q * (w : ℚ) ^ k := by
  rw [(div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp (Rat.num_div_den q), hd]; grind

/-- The numerator of a rational with square denominator `w²` is prime to any `p ∣ w`: since
`num`, `den` are coprime and `w² = den`, a prime dividing both `num` and `w` would be a unit. -/
private theorem not_dvd_num {q : ℚ} {w : ℤ} (hd : (q.den : ℤ) = w ^ 2) (hpw : (p : ℤ) ∣ w) :
    ¬ (p : ℤ) ∣ q.num := by
  intro hdvd
  have hcop : IsCoprime q.num (w ^ 2) := by
    rw [← hd, Int.isCoprime_iff_nat_coprime]; simpa using q.reduced
  exact absurd (Int.isUnit_iff.mp
    (hcop.isUnit_of_dvd' hdvd (hpw.trans (dvd_pow_self w two_ne_zero))))
    (by have := (Fact.out : p.Prime).two_le; lia)

/-- Numerator valuation of the kernel certificate: with `v_p(N) < v_p(K)`, the numerator
`N² - M·K²` is nonzero with `v_p = 2·v_p(N)`, since the second term has strictly larger valuation
(`K²` alone already dominates `N²`). -/
private theorem padicValRat_num_cert {N K M : ℤ} (hcrux : padicValInt p N < padicValInt p K)
    (hN0 : N ≠ 0) (hK0 : K ≠ 0) :
    padicValRat p ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ) = (2 * padicValInt p N : ℤ)
      ∧ (N ^ 2 - M * K ^ 2 : ℤ) ≠ 0 := by
  have hK2 : padicValInt p (K ^ 2) = 2 * padicValInt p K := by
    rw [pow_two, padicValInt.mul hK0 hK0]; grind
  have hNval2 : padicValInt p (N ^ 2) = 2 * padicValInt p N := by
    rw [pow_two, padicValInt.mul hN0 hN0]; grind
  have hqv : padicValRat p ((N ^ 2 : ℤ) : ℚ) = (2 * padicValInt p N : ℤ) := by
    rw [padicValRat.of_int, hNval2]; grind
  rcases eq_or_ne (M * K ^ 2 : ℤ) 0 with h0 | h0
  · rw [h0, sub_zero]; exact ⟨hqv, pow_ne_zero 2 hN0⟩
  · have hsplit : ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ)
        = ((N ^ 2 : ℤ) : ℚ) + (-((M * K ^ 2 : ℤ) : ℚ)) := by grind
    have hq0 : ((N ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hN0
    have hr0 : (-((M * K ^ 2 : ℤ) : ℚ)) ≠ 0 := by
      have : ((M * K ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h0
      simpa using this
    have hlt : padicValRat p ((N ^ 2 : ℤ) : ℚ)
        < padicValRat p (-((M * K ^ 2 : ℤ) : ℚ)) := by
      rw [hqv, padicValRat.neg, padicValRat.of_int]
      have hle := padicValInt_mono p (a := K ^ 2) (b := M * K ^ 2) ⟨M, by ring⟩ h0
      rw [hK2] at hle
      lia
    have hqrne : ((N ^ 2 : ℤ) : ℚ) + (-((M * K ^ 2 : ℤ) : ℚ)) ≠ 0 := fun he => by
      have heq : ((N ^ 2 : ℤ) : ℚ) = ((M * K ^ 2 : ℤ) : ℚ) := by grind
      rw [heq, padicValRat.neg] at hlt
      exact lt_irrefl _ hlt
    refine ⟨by rw [hsplit, padicValRat.add_eq_of_lt hqrne hq0 hr0 hlt, hqv], ?_⟩
    intro he
    apply hqrne
    rw [← hsplit]
    exact_mod_cast he

/-- Coordinate data for a kernel point. If `(x, y)` satisfies the curve equation and reduces to
the origin (`p ∣ x.den`), it has integer coordinates `x = x.num/w²`, `y = y.num/w³` over a common
`w` with `p ∣ w`, `w ≠ 0` and `p`-unit numerator `x.num`. -/
private theorem kernel_point_data {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hd : (x.den : ZMod p) = 0) :
    ∃ w : ℤ, (x.num : ℚ) = x * (w : ℚ) ^ 2 ∧ (y.num : ℚ) = y * (w : ℚ) ^ 3
      ∧ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) ∣ x.num ∧ w ≠ 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hxd, hyd⟩ := den_isSquare a₂ a₄ a₆ h
  have hpw : (p : ℤ) ∣ (w : ℤ) := by
    exact_mod_cast hp.dvd_of_dvd_pow (hxd ▸ (ZMod.natCast_eq_zero_iff _ p).mp hd)
  have hwne : (w : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Rat.ne_zero_of_den_eq_pow two_ne_zero hxd)
  exact ⟨w, cast_num_eq hxd, cast_num_eq hyd, hpw,
    not_dvd_num p (by grind) hpw, hwne⟩

/-- Integer form of the curve relation for a point `(A/E², B/E³)`: clearing denominators of
`y² = x³ + a₂x² + a₄x + a₆` gives `B² = A³ + a₂A²E² + a₄AE⁴ + a₆E⁶`. -/
private theorem int_curve_relation {x y : ℚ} {A B E : ℤ}
    (hcv : y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ))
    (hA : (A : ℚ) = x * (E : ℚ) ^ 2) (hB : (B : ℚ) = y * (E : ℚ) ^ 3) :
    B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 := by
  have hq : (B : ℚ) ^ 2 = (A : ℚ) ^ 3 + a₂ * (A : ℚ) ^ 2 * (E : ℚ) ^ 2
      + a₄ * (A : ℚ) * (E : ℚ) ^ 4 + a₆ * (E : ℚ) ^ 6 := by
    grind
  exact_mod_cast hq

omit [Fact p.Prime] in
/-- The certificate scalar `W = -A²C² + a₄ACE²G² + a₆E²G²(AG² + CE²)` is a `p`-unit: it is
`≡ -A²C²` mod `p` (the other terms carry the factor `E`), and `A`, `C` are `p`-units. -/
private theorem not_dvd_W_cert {A C E G : ℤ} (hpZ : Prime (p : ℤ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C) (hpE : (p : ℤ) ∣ E) :
    ¬ (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2)) := by
  intro hdvd
  have hrest : (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2) := by
    have heq : -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
          + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2
        = E ^ 2 * G ^ 2 * (a₄ * A * C + a₆ * (A * G ^ 2 + C * E ^ 2)) := by grind
    rw [heq]
    exact ((hpE.trans (dvd_pow_self E two_ne_zero)).mul_right (G ^ 2)).mul_right _
  have hAC : (p : ℤ) ∣ A ^ 2 * C ^ 2 := by simpa using dvd_sub hrest hdvd
  grind [Prime.dvd_of_dvd_pow, Prime.dvd_mul]

/-- The certificate scalar `K = A·G² - C·E²` is nonzero when `x₁ ≠ x₂`: `K = 0` forces
`x₁·E²G² = x₂·E²G²` and hence `x₁ = x₂`. -/
private theorem K_ne_zero {x₁ x₂ : ℚ} {A C E G : ℤ} (hne : x₁ ≠ x₂)
    (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2)
    (hEQ : (E : ℚ) ≠ 0) (hGQ : (G : ℚ) ≠ 0) :
    A * G ^ 2 - C * E ^ 2 ≠ 0 := fun h => hne <| by
  have h0 : ((A * G ^ 2 - C * E ^ 2 : ℤ) : ℚ) = 0 := by rw [h]; simp
  push_cast at h0
  grind [mul_right_cancel₀, pow_ne_zero]

/-- Final valuation step of the kernel-closure certificate. Given the single-fraction
`x₃ = (N² - M·K²)/(A·C·K²)` with `p`-unit `A`, `C` and the crux `v_p(N) < v_p(K)`, the `p`-adic
valuation of `x₃` is `2·(v_p N - v_p K) < 0`, hence `p ∣ x₃.den`. -/
private theorem den_zero_of_cert {x₃ : ℚ} {A C K N M : ℤ}
    (hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hcrux : padicValInt p N < padicValInt p K)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (hK0 : K ≠ 0) (hN0 : N ≠ 0) :
    (x₃.den : ZMod p) = 0 := by
  obtain ⟨hNumvalQ, hNum0⟩ := padicValRat_num_cert (M := M) p hcrux hN0 hK0
  have hDenval : padicValInt p (A * C * K ^ 2) = 2 * padicValInt p K := by
    rw [padicValInt.mul (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0), padicValInt.mul hA0 hC0,
      padicValInt.eq_zero_of_not_dvd hpA, padicValInt.eq_zero_of_not_dvd hpC,
      pow_two, padicValInt.mul hK0 hK0]
    grind
  have hDen3Q : ((A * C * K ^ 2 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0))
  have hx3div : x₃ = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ) / ((A * C * K ^ 2 : ℤ) : ℚ) := by
    rw [eq_div_iff hDen3Q]; exact hMain
  have hx3neg : padicValRat p x₃ < 0 := by
    rw [hx3div, padicValRat.div (by exact_mod_cast hNum0) hDen3Q, hNumvalQ, padicValRat.of_int,
      hDenval]
    grind
  have hden0 : padicValNat p x₃.den ≠ 0 := by rw [padicValRat_def] at hx3neg; lia
  exact (ZMod.natCast_eq_zero_iff _ p).mpr
    ((dvd_iff_padicValNat_ne_zero x₃.den_ne_zero).mpr hden0)

/-- The single-fraction identity `x₃·(A·C·K²) = N² - a₆E²G²K²` for the doubled `x`-coordinate,
where `K = AG² - CE²`, `N = ADE - BCG`. It follows from the slope relation `hℓ` and the two
curve relations by clearing denominators. -/
private theorem addX_single_fraction {x₁ y₁ x₂ y₂ ℓ x₃ : ℚ} {A B C D E G : ℤ}
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂) (haddX : x₃ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂)
    (hcv1 : y₁ ^ 2 = x₁ ^ 3 + (a₂ : ℚ) * x₁ ^ 2 + (a₄ : ℚ) * x₁ + (a₆ : ℚ))
    (hcv2 : y₂ ^ 2 = x₂ ^ 3 + (a₂ : ℚ) * x₂ ^ 2 + (a₄ : ℚ) * x₂ + (a₆ : ℚ))
    (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hB : (B : ℚ) = y₁ * (E : ℚ) ^ 3)
    (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2) (hD : (D : ℚ) = y₂ * (G : ℚ) ^ 3) :
    x₃ * ((A * C * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ)
      = (((A * D * E - B * C * G) ^ 2
        - a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ) := by
  rw [haddX]
  push_cast
  rw [hA, hB, hC, hD]
  linear_combination
    ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₁ * x₂ * (ℓ * x₁ - ℓ * x₂ + y₁ - y₂))) * hℓ
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₂ * (x₁ - x₂))) * hcv1
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (-x₁ * (x₁ - x₂))) * hcv2

/-- The crux valuation inequality of the kernel-closure certificate, isolated from the integer
curve relations. With `K = AG² - CE²`, `N = ADE - BCG` and the `p`-unit `W = -A²C² + …`, the
identity `N·(ADE + BCG) = K·W` (from the two curve relations) together with `p ∣ E`, `p ∣ G` and
`p`-unit `A`, `C` gives `N ≠ 0`, `K ≠ 0` and `v_p(N) < v_p(K)`. -/
private theorem crux_of_int_relations {A B C D E G : ℤ} {x₁ x₂ : ℚ} (hpZ : Prime (p : ℤ))
    (hne : x₁ ≠ x₂) (hA : (A : ℚ) = x₁ * (E : ℚ) ^ 2) (hC : (C : ℚ) = x₂ * (G : ℚ) ^ 2)
    (hEne : (E : ℚ) ≠ 0) (hGne : (G : ℚ) ≠ 0) (hpE : (p : ℤ) ∣ E) (hpG : (p : ℤ) ∣ G)
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6)
    (hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6) :
    padicValInt p (A * D * E - B * C * G) < padicValInt p (A * G ^ 2 - C * E ^ 2)
      ∧ A * D * E - B * C * G ≠ 0 ∧ A * G ^ 2 - C * E ^ 2 ≠ 0 := by
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  set W : ℤ := -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
    + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) with hWdef
  have hI2 : N * (A * D * E + B * C * G) = K * W := by
    grind
  have hpS : (p : ℤ) ∣ (A * D * E + B * C * G) :=
    dvd_add (hpE.mul_left (A * D)) (hpG.mul_left (B * C))
  have hpW : ¬ (p : ℤ) ∣ W := hWdef ▸ not_dvd_W_cert a₄ a₆ p hpZ hpA hpC hpE
  have hW0 : W ≠ 0 := fun h => hpW (h ▸ dvd_zero _)
  have hK0 : K ≠ 0 := hKdef ▸ K_ne_zero hne hA hC hEne hGne
  have hprodne : N * (A * D * E + B * C * G) ≠ 0 := hI2 ▸ mul_ne_zero hK0 hW0
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hprodne
  exact ⟨padicValInt_lt_of_mul_eq p hI2 hpS hpW hN0 (right_ne_zero_of_mul hprodne) hK0 hW0,
    hN0, hK0⟩

/-- The kernel of reduction is closed under the group law. If two affine points `P`, `Q`
both reduce to the origin mod `p` (`p ∣ x₁.den` and `p ∣ x₂.den`) but are distinct over `ℚ`, then
their sum also reduces to the origin: the `x`-coordinate `x₃ = addX x₁ x₂ (slope …)` of `P + Q`
again has `p ∣ x₃.den`.

This is the one genuinely `p`-adic corner of `red_p` additivity. It is proved by an explicit
single-fraction certificate: writing `x_i = A_i / w_i²`, `y_i = B_i / w_i³` (`den_isSquare`) with
`E = w₁`, `G = w₂`, `p ∣ E`, `p ∣ G`, the group law gives the integer identity
`x₃ = (N² - a₆E²G²K²) / (A·C·K²)` where `K = A·G² - C·E²` and `N = A·D·E - B·C·G`. The secant
intercept `ν = N / (E·G·K)` satisfies `N·(A·D·E + B·C·G) = K·W` with `W ≡ -A²C²` a `p`-unit
(both integer identities follow from the two curve relations), so `v_p(N) < v_p(K)`. Tracking
`padicValRat` through the fraction yields `padicValRat p x₃ = 2·(v_p N - v_p K) < 0`, i.e.
`p ∣ x₃.den`. -/
private theorem den_addX_both_kernel {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hne : x₁ ≠ x₂) (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    grind [WeierstrassCurve.Affine.slope_of_X_ne]
  have haddX : x₃ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    rw [hx3def]; simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hcv1 := curve_equation_iff a₂ a₄ a₆ h₁
  have hcv2 := curve_equation_iff a₂ a₄ a₆ h₂
  obtain ⟨E, hA, hB, hpE, hpA, hEne⟩ := kernel_point_data a₂ a₄ a₆ p h₁ hd1
  obtain ⟨G, hC, hD, hpG, hpC, hGne⟩ := kernel_point_data a₂ a₄ a₆ p h₂ hd2
  set A : ℤ := x₁.num
  set B : ℤ := y₁.num
  set C : ℤ := x₂.num
  set D : ℤ := y₂.num
  -- integer curve relations
  have hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 :=
    int_curve_relation a₂ a₄ a₆ hcv1 hA hB
  have hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6 :=
    int_curve_relation a₂ a₄ a₆ hcv2 hC hD
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  -- the single-fraction identity for the final valuation certificate
  have hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) := by
    rw [hKdef, hNdef]; exact addX_single_fraction a₂ a₄ a₆ hℓ haddX hcv1 hcv2 hA hB hC hD
  -- the crux inequality `v_p(N) < v_p(K)`, with nonzeroness, from the integer curve relations
  obtain ⟨hcrux, hN0, hK0⟩ := crux_of_int_relations a₂ a₄ a₆ p hpZ hne hA hC
    (by exact_mod_cast hEne) (by exact_mod_cast hGne) hpE hpG hpA hpC hCR1 hCR2
  exact den_zero_of_cert (M := a₆ * E ^ 2 * G ^ 2) p hMain hpA hpC hcrux
    (fun h => hpA (h ▸ dvd_zero _)) (fun h => hpC (h ▸ dvd_zero _)) hK0 hN0

/-- Distinct points sharing an `x`-coordinate are mutually negative: if `x₁ = x₂` but
`(x₁, y₁) ≠ (x₂, y₂)`, then `y₁ = negY x₂ y₂` (so `P + Q = O`). -/
private theorem y_eq_negY_of_X_eq {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hx12 : x₁ = x₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
  have := WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12
  grind [Affine.Point.some.injEq]

/-- Reduced-curve negation is `Y ↦ -Y`, since `a₁ = a₃ = 0` for the integral model. -/
@[grind =]
private theorem reduced_negY (X Y : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY X Y = -Y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ (by simp [WeierstrassCurve.map, curveℤ])
    (by simp [WeierstrassCurve.map, curveℤ]) X Y

/-- If the doubled `x`-coordinate `addX x₁ x₂ (slope …)` survives reduction, so does the slope:
from `ℓ² = addX + a₂ + x₁ + x₂` a nonzero `addX`-denominator forces a nonzero `ℓ`-denominator. -/
private theorem slope_den_of_addX_den
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have he : (ℓ : ℚ) ^ 2 = (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + (a₂ : ℚ) + x₁ + x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [he]; exact den_add_ne_zero (den_add_ne_zero (den_add_ne_zero hd3 (by simp)) hd1) hd2
  rw [Rat.den_pow, Nat.cast_pow] at hℓ2
  exact fun h => hℓ2 (by grind)

/-- Tangent-mod-`p` additivity, `2`-torsion sub-case: the shared reduced point is `2`-torsion
(`Ȳ₁ = -Ȳ₁`), so both `red_p (P + Q)` and `P̄ + P̄` are the origin. The doubled `x`-coordinate
must have vanishing denominator mod `p`, else the reduced slope forces `f'(X̄₁) = 0`, contradicting
nonsingularity of the reduced point. -/
private theorem red_p_add_tangent_two_torsion (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = (x₂ : ZMod p)) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p))
    (hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, Affine.Point.add_of_Y_eq rfl hYneg,
    Affine.Point.add_of_X_ne hne]
  apply red_p_of_den_zero a₂ a₄ a₆ p hΔ
    (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hne hxy.left))
  by_contra hd3_s
  obtain ⟨-, htan⟩ :=
    reduced_tangent_eqs a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2
      (slope_den_of_addX_den a₂ a₄ a₆ p hd1 hd2 hd3_s) hd3_s
  have hYeq : (y₁ : ZMod p) = -(y₁ : ZMod p) := hYneg.trans (reduced_negY a₂ a₄ a₆ p _ _)
  have hY0 : (y₁ : ZMod p) + (y₂ : ZMod p) = 0 := by grind
  rw [hY0, mul_zero] at htan
  have hfd : 3 * (x₁ : ZMod p) ^ 2 + 2 * (a₂ : ZMod p) * (x₁ : ZMod p) + (a₄ : ZMod p) = 0 := by
    grind
  have hns : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Nonsingular
      (x₁ : ZMod p) (y₁ : ZMod p) :=
    red_nonsingular_affine a₂ a₄ a₆ p hΔ h₁
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
      (mt (Rat.den_cast_eq_zero_iff two_ne_zero
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1).mpr hd1)
  rw [WeierstrassCurve.Affine.nonsingular_iff, map_curveℤ_zmod] at hns
  simp only [zero_mul, sub_zero] at hns
  exact hns.2.elim (fun hfd_ne => (Ne.symm hfd_ne) hfd) (fun hyne2 => hyne2 hYeq)

/-- The doubled `x`-coordinate `addX x₁ x₂ ℓ` survives reduction when the slope, `x₁` and `x₂`
all do: `addX = ℓ² - a₂ - x₁ - x₂` has nonzero denominator mod `p`. -/
private theorem addX_den_ne {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
  rw [haddX]
  exact den_sub_ne_zero (den_sub_ne_zero (den_sub_ne_zero
    (by rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero 2 hℓden) (by simp)) hd1) hd2

/-- In the genuine-tangent case the reduced secant slope equals the reduced tangent slope `ℓ`:
`slope X̄₁ X̄₁ Ȳ₁ Ȳ₁ = ℓ`, matched via the reduced tangent identity `htan` and `X̄₁ = X̄₂`. -/
private theorem reduced_slope_eq {ℓ : ZMod p} {x₁ x₂ y₁ y₂ : ZMod p}
    (hYneg : ¬ y₁ = ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY x₁ y₁)
    (h2Yne : y₁ + y₁ ≠ 0) (hXbar : x₁ = x₂) (hYbar : y₁ = y₂)
    (htan : ℓ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.slope x₁ x₁ y₁ y₁ = ℓ := by
  refine mul_right_cancel₀ h2Yne ?_
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYneg]
  simp only [map_curveℤ_zmod, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add]
  rw [div_mul_cancel₀ _ h2Yne]
  grind

/-- The reduced-curve `addY` at a doubled point unfolds to `-(ℓ·(addX - X̄₁) + Ȳ₁)`. -/
private theorem reduced_addY_eq (X Y L : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addY X X Y L
      = -(L * (((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L - X)
        + Y) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, map_curveℤ_zmod]; grind

/-- The reduced-curve `addX` at a doubled point unfolds to `L² - a₂ - X - X`. -/
private theorem reduced_addX_eq (X L : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.addX X X L
      = L ^ 2 - (a₂ : ZMod p) - X - X := by
  simp only [WeierstrassCurve.Affine.addX, map_curveℤ_zmod]; grind

/-- The cast of the rational `addY` matches the reduced `addY` form when the slope, `x`-coordinates
and `y`-coordinate all survive reduction: the denominators of each summand are nonzero mod `p`, so
`Rat.cast` distributes over the `-(ℓ·(addX - x₁) + y₁)` expression. -/
private theorem addY_cast_eq {x₁ y₁ x₂ ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hdy1 : (y₁.den : ZMod p) ≠ 0)
    (hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0) :
    ((curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
      = -((ℓ : ZMod p) * (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p) - (x₁ : ZMod p))
        + (y₁ : ZMod p)) := by
  have haddY : (curve a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, curve]; grind
  rw [haddY, Rat.cast_neg,
    Rat.cast_add_of_ne_zero (den_mul_ne_zero hℓden (den_sub_ne_zero hd3 hd1)) hdy1,
    Rat.cast_mul_of_ne_zero hℓden (den_sub_ne_zero hd3 hd1), Rat.cast_sub_of_ne_zero hd3 hd1]

/-- Tangent-mod-`p` additivity, genuine-tangent sub-case (`Ȳ₁ + Ȳ₂ ≠ 0`): the reduced sum
`red_p (P + Q)` is the tangent doubling of the common reduced point `P̄`. Both reduced `x`- and
`y`-coordinates are matched against the doubling formulas via the reduced tangent identities. -/
private theorem red_p_add_tangent_generic (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = (x₂ : ZMod p)) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p))
    (hYneg : ¬ (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  have hslX : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
    WeierstrassCurve.Affine.slope_of_X_ne hne
  set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂) with hℓdef
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0 := by
    intro h; grind
  have hℓden_s : (((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 :=
    reduced_slope_den a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hy2
  have hℓden : (ℓ.den : ZMod p) ≠ 0 := by rwa [← hslX]
  have hd3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 :=
    addX_den_ne a₂ a₄ a₆ p hℓden hd1 hd2 haddX
  have hd3_s : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0 := by rwa [hslX]
  obtain ⟨hS2, htan⟩ :=
    reduced_tangent_eqs a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
  rw [hslX] at hS2 htan
  have h2Yne : (y₁ : ZMod p) + (y₁ : ZMod p) ≠ 0 := by
    intro h; grind
  have hℓd := reduced_slope_eq a₂ a₄ a₆ p hYneg h2Yne hXbar hYbar htan
  have hxeq : ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ : ZMod p)
      = (ℓ : ZMod p) ^ 2 - (a₂ : ZMod p) - (x₁ : ZMod p) - (x₁ : ZMod p) := by
    grind
  have hy3cast := addY_cast_eq a₂ a₄ a₆ p (x₂ := x₂) hℓden hd1 hdy1 hd3
  rw [Affine.Point.add_of_X_ne hne,
    red_p_of_den_ne a₂ a₄ a₆ p hΔ
      (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hne hxy.left)) hd3_s,
    red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, Affine.Point.add_of_Y_ne hYneg, Affine.Point.some.injEq]
  refine ⟨by rw [hslX, hℓd, hxeq, reduced_addX_eq], ?_⟩
  rw [hslX, hy3cast, hℓd, reduced_addY_eq, reduced_addX_eq, hxeq]

/-- Additivity when both summands reduce to the origin (`p ∣ x₁.den`, `p ∣ x₂.den`): the sum
reduces to `O` too. If `x₁ = x₂` then `Q = -P` and `P + Q = 0`; otherwise `x₁ ≠ x₂` and the
kernel-closure certificate `den_addX_both_kernel` gives `p ∣ x₃.den`. -/
private theorem red_p_add_kernel (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  by_cases hx12 : x₁ = x₂
  · rw [Affine.Point.add_of_Y_eq hx12 (y_eq_negY_of_X_eq a₂ a₄ a₆ h₁ h₂ hx12 hPQ), red_p_zero]
  · rw [Affine.Point.add_of_X_ne hx12]
    exact red_p_of_den_zero a₂ a₄ a₆ p hΔ _
      (den_addX_both_kernel a₂ a₄ a₆ p h₁.1 h₂.1 hx12 hd1 hd2)

/-- Additivity when the reduced points coincide and `Q = -P` over `ℚ` (`x₁ = x₂`): then `P + Q = 0`
and the common reduced point is `2`-torsion, so `red_p (P + Q) = 0 = P̄ + P̄`. -/
private theorem red_p_add_neg (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hx12 : x₁ = x₂) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p)) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  have hy : y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := y_eq_negY_of_X_eq a₂ a₄ a₆ h₁ h₂ hx12 hPQ
  rw [Affine.Point.add_of_Y_eq hx12 hy, red_p_zero, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1]
  have hyneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p) := by
    have hny : (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ = -y₂ := negY_curve x₂ y₂
    have hcast : (y₁ : ZMod p) = -(y₂ : ZMod p) := by rw [hy, hny, Rat.cast_neg]
    grind
  rw [Affine.Point.add_of_Y_eq rfl hyneg]

/-- Additivity of `red_p` in the tangent-mod-`p` configuration (S4): when two affine points
`P`, `Q` reduce to the same point of `E/𝔽ₚ` (`red_p P = red_p Q`) but are distinct over `ℚ`, the
reduction of their rational sum equals the sum of their reductions. -/
private theorem red_p_add_tangent (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hred : red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) = red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
  by_cases hd1 : (x₁.den : ZMod p) = 0
  · -- `P → O`, hence (by `hred`) `Q → O` as well; the sum reduces to `O`.
    have hQ0 : red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) = 0 := by
      rw [← hred]; exact red_p_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1
    have hd2 : (x₂.den : ZMod p) = 0 := by
      grind [red_p_of_den_ne, Affine.Point.some_ne_zero]
    rw [red_p_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1, hQ0, add_zero]
    exact red_p_add_kernel a₂ a₄ a₆ p hΔ h₁ h₂ hPQ hd1 hd2
  · -- `P` has good reduction; then so does `Q`, and they share reduced coordinates.
    have hd2 : (x₂.den : ZMod p) ≠ 0 := by
      grind [red_p_of_den_ne, red_p_of_den_zero, Affine.Point.some_ne_zero]
    have hdy1 : (y₁.den : ZMod p) ≠ 0 := ydenom_ne_zero h₁.1 hd1
    have hdy2 : (y₂.den : ZMod p) ≠ 0 := ydenom_ne_zero h₂.1 hd2
    rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
      Affine.Point.some.injEq] at hred
    obtain ⟨hXbar, hYbar⟩ := hred
    -- Rewrite `red Q` to `red P` throughout: the two reduced points coincide.
    have hQeqP : red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
      rw [red_p_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, red_p_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
        Affine.Point.some.injEq]
      exact ⟨hXbar.symm, hYbar.symm⟩
    rw [hQeqP]
    by_cases hx12 : x₁ = x₂
    · -- `Q = -P`, so `P + Q = 0`, and the common reduced point is `2`-torsion.
      exact red_p_add_neg a₂ a₄ a₆ p hΔ h₁ h₂ hPQ hd1 hx12 hYbar
    · -- `x₁ ≠ x₂` over `ℚ` but the reduced points coincide: the tangent-mod-`p` case, split on
      -- whether the common reduced point is `2`-torsion.
      by_cases hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
          (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)
      · exact red_p_add_tangent_two_torsion a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg
      · exact red_p_add_tangent_generic a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg

/-- `repr` of an affine `some` point is `ℤ → ZMod p` applied to its integer representative. -/
private theorem repr_some_eq (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    repr a₂ a₄ a₆ p (.some x y h)
      = (Int.castRingHom (ZMod p)) ∘ Trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose :=
  rfl

/-- Additivity of `red_p` on `some + some` when the two reduced representatives are proportional
mod `p` and the points are equal over `ℚ` (case S1): the reduced sum is an honest doubling. -/
private theorem red_p_map_add_double (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘
      Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose))
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁))
      = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₁ y₁ h₁)
      ≈ (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hgadd : (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁)
      = (curve a₂ a₄ a₆).toProjective.add ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
          ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁) := by
    rw [Projective.add_self, ← map_curveℤ_ℚ]
    exact (Projective.map_dblXYZ (Int.castRingHom ℚ) _).symm
  exact sum_repr_equiv a₂ a₄ a₆ p hΔ _ _ hns1 hns1 hgadd
    (toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1')
    (toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1') hadd

/-- Additivity of `red_p` on `some + some` in the secant case (`¬ repr P ≈ repr Q` mod `p`): the
reduced sum is a secant, and the two representatives are also inequivalent over `ℚ`. -/
private theorem red_p_map_add_secant (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘
      Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose))
    (hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘
      Trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose))
    (heq : ¬ (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ
          (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)
          (Trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  set w₂ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hden2 : x₂.den = w₂ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.1
  have hden2' : y₂.den = w₂ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.2
  have hℚne : ¬ ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁) ≈ ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂) := by
    intro hℚeq
    apply heq
    have hpt : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂ := by
      rw [← toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1', ← toAffine_g_Trep a₂ a₄ a₆ h₂ hden2 hden2']
      exact Projective.Point.toAffine_of_equiv hℚeq
    exact hpt ▸ Setoid.refl (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁))
  have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
      = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂) := by
    rw [Projective.add_of_not_equiv heq, repr_some_eq, repr_some_eq]
    exact Projective.map_addXYZ (Int.castRingHom (ZMod p)) _ _
  have hgaddXYZ : (curve a₂ a₄ a₆).toProjective.addXYZ ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
        ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂)
      = (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
          (Trep x₂ y₂ w₂) := by
    rw [← map_curveℤ_ℚ]; exact Projective.map_addXYZ (Int.castRingHom ℚ) _ _
  have hgadd : (Int.castRingHom ℚ) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (Trep x₁ y₁ w₁)
        (Trep x₂ y₂ w₂)
      = (curve a₂ a₄ a₆).toProjective.add ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁)
          ((Int.castRingHom ℚ) ∘ Trep x₂ y₂ w₂) := by
    rw [← hgaddXYZ]; exact (Projective.add_of_not_equiv hℚne).symm
  exact sum_repr_equiv a₂ a₄ a₆ p hΔ _ _ hns1 hns2 hgadd
    (toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1') (toAffine_g_Trep a₂ a₄ a₆ h₂ hden2 hden2') hadd

/-- Additivity of `red_p` on `some + some` in the tangent-mod-`p` case (S4): the reduced
representatives are proportional but the points differ over `ℚ`. The projective-class goal is
reduced to the affine additivity supplied by `red_p_add_tangent`. -/
private theorem red_p_map_add_tangent_case (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (heq : (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂)))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
      = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose) := by
  have hred : red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) = red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
    rw [red_p_eq_toAffine, red_p_eq_toAffine]; exact Projective.Point.toAffine_of_equiv heq
  have hnspV : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      ((Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
        (Trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) := by
    rw [← hadd]
    exact Projective.nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)
  refine Projective.equiv_of_toAffine_eq (repr_nonsingular a₂ a₄ a₆ p hΔ _) hnspV ?_
  rw [← red_p_eq_toAffine a₂ a₄ a₆ p hΔ, ← hadd,
    Projective.Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _),
    ← red_p_eq_toAffine a₂ a₄ a₆ p hΔ, ← red_p_eq_toAffine a₂ a₄ a₆ p hΔ]
  exact red_p_add_tangent a₂ a₄ a₆ p hΔ h₁ h₂ hred hPQ

/-- Additivity of the reduction map on two `some` points, reduced to a projective-class
equivalence and dispatched to the doubling, tangent-mod-`p` and secant sub-cases. -/
private theorem red_p_map_add_some (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + red_p a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ Trep x₁ y₁ w₁) :=
    nonsingular_of_toAffine_some a₂ a₄ a₆ (toAffine_g_Trep a₂ a₄ a₆ h₁ hden1 hden1')
  have hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘
      Trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose) :=
    nonsingular_of_toAffine_some a₂ a₄ a₆ (toAffine_g_Trep a₂ a₄ a₆ h₂
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.1
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.2)
  rw [red_p_eq_toAffine, red_p_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁),
    red_p_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂),
    ← Projective.Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)]
  refine Projective.Point.toAffine_of_equiv ?_
  by_cases heq : (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
  · -- `repr P ≈ repr Q` mod `p`: the reduced sum is a doubling of `repr P`.
    have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
          (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
        = (Int.castRingHom (ZMod p)) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (Trep x₁ y₁ w₁) := by
      rw [Projective.add_of_equiv heq, repr_some_eq]
      exact Projective.map_dblXYZ (Int.castRingHom (ZMod p)) _
    rw [hadd]
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂
    · rw [← hPQ] at hadd ⊢; exact red_p_map_add_double a₂ a₄ a₆ p hΔ h₁ hns1 hadd
    · exact red_p_map_add_tangent_case a₂ a₄ a₆ p hΔ h₁ h₂ heq hPQ hadd
  · rw [Projective.add_of_not_equiv heq, repr_some_eq, repr_some_eq,
      Projective.map_addXYZ (Int.castRingHom (ZMod p))]
    exact red_p_map_add_secant a₂ a₄ a₆ p hΔ h₁ h₂ hns1 hns2 heq

/-- Additivity of the reduction map. -/
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
  | some x₂ y₂ h₂ => exact red_p_map_add_some a₂ a₄ a₆ p hΔ h₁ h₂

/-- The reduction map bundled as an additive homomorphism
`(curve …).toAffine.Point →+ (reducedCurve …).toAffine.Point`. -/
@[simps]
noncomputable def redHom (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point where
  toFun := red_p a₂ a₄ a₆ p hΔ
  map_zero' := red_p_zero a₂ a₄ a₆ p hΔ
  map_add' := red_p_map_add a₂ a₄ a₆ p hΔ

end ECCompute
