/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.RedP
import ECCompute.Theory.Descent.Reduction.KernelClosure
import ECCompute.Theory.Descent.Reduction.ReducedSlope
import ECCompute.Theory.Descent.ReducedArith
import ECCompute.ForMathlib.WeierstrassCurveProjective

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

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]

@[grind =]
private theorem reduced_negY (X Y : ZMod p) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.negY X Y = -Y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ (by simp [WeierstrassCurve.map, curveℤ])
    (by simp [WeierstrassCurve.map, curveℤ]) X Y

/-! ### The fixed projective representative -/

/-- The fixed `ZMod p`-projective representative of an affine point used to compute `red_p`:
`![0, 1, 0]` for the origin, and `ℤ → ZMod p` applied to the integer representative otherwise. -/
private noncomputable def repr :
    (curve a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h =>
      (Int.castRingHom (ZMod p)) ∘ Trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose

/-- `repr` of an affine `some` point is `ℤ → ZMod p` applied to its integer representative. -/
private theorem repr_some_eq (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    repr a₂ a₄ a₆ p (.some x y h)
      = (Int.castRingHom (ZMod p)) ∘ Trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose :=
  rfl

/-- `repr P` is a nonsingular representative on the reduced curve. -/
private theorem repr_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
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
private theorem red_p_eq_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    red_p a₂ a₄ a₆ p hΔ P
      = Projective.Point.toAffine ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective
          (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact (Projective.Point.toAffine_zero).symm
  | some x y h => rfl

/-- Over `ℚ`, the affine point underlying the integer representative `Trep x y w` is `(x, y)`. -/
private theorem toAffine_g_Trep {x y : ℚ} {w : ℕ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ Trep x y w)
      = .some x y h := by
  have hw : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.ne_zero_of_den_eq_pow two_ne_zero hden)
  rw [Trep_map_ℚ hden hden',
    Projective.Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (pow_ne_zero 3 hw)),
    Projective.Point.toAffine_some ((Projective.nonsingular_some x y).mpr h)]

/-- An integer projective representative whose rational affine point is a `some` is nonsingular
over `ℚ` (the affine point of a singular representative is the origin). -/
private theorem nonsingular_of_toAffine_some {U : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hU : Projective.Point.toAffine (curve a₂ a₄ a₆).toProjective ((Int.castRingHom ℚ) ∘ U)
      = .some X Y hR) :
    (curve a₂ a₄ a₆).toProjective.Nonsingular ((Int.castRingHom ℚ) ∘ U) := by
  grind [Projective.Point.toAffine_of_singular, Affine.Point.some_ne_zero]

/-- If two integer projective representatives have the same (rational) affine point, then they are
proportional over `ℤ`, with the cross scalars given by each other's `Z`-coordinate. -/
private theorem int_smul_eq_of_toAffine_eq {S T : Fin 3 → ℤ} {X Y : ℚ}
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
private theorem repr_equiv_of_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
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
private theorem sum_repr_equiv (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {V : Fin 3 → ℤ}
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

/-- The integral model maps to the rational curve under `ℤ → ℚ`. -/
private theorem map_curveℤ_ℚ :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom ℚ) = curve a₂ a₄ a₆ := by
  rw [← baseChange_curveℤ_ℚ, WeierstrassCurve.baseChange, algebraMap_int_eq]

/-! ### Case analysis for the group law -/

/-- Distinct points sharing an `x`-coordinate are mutually negative: if `x₁ = x₂` but
`(x₁, y₁) ≠ (x₂, y₂)`, then `y₁ = negY x₂ y₂` (so `P + Q = O`). -/
private theorem y_eq_negY_of_X_eq {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hx12 : x₁ = x₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
  have := WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12
  grind [Affine.Point.some.injEq]

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
  have hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0 := by grind
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
  have h2Yne : (y₁ : ZMod p) + (y₁ : ZMod p) ≠ 0 := by grind
  have hℓd := reduced_slope_eq a₂ a₄ a₆ p hYneg h2Yne hXbar hYbar htan
  have hy3cast := addY_cast_eq a₂ a₄ a₆ p (x₂ := x₂) hℓden hd1 hdy1 hd3
  have hns3 := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hne hxy.left)
  grind [Affine.Point.add_of_X_ne, red_p_of_den_ne, Affine.Point.add_of_Y_ne,
    Affine.Point.some.injEq, reduced_addX_eq, reduced_addY_eq]

/-- Additivity when both summands reduce to the origin (`p ∣ x₁.den`, `p ∣ x₂.den`): the sum
reduces to `O` too. If `x₁ = x₂` then `Q = -P` and `P + Q = 0`; otherwise `x₁ ≠ x₂` and the
kernel-closure certificate `den_addX_both_kernel` gives `p ∣ x₃.den`. -/
private theorem red_p_add_kernel (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    red_p a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  obtain rfl | hx12 := eq_or_ne x₁ x₂
  · rw [Affine.Point.add_of_Y_eq rfl (y_eq_negY_of_X_eq a₂ a₄ a₆ h₁ h₂ rfl hPQ), red_p_zero]
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

/-- Additivity of `red_p` when two affine points `P`, `Q` reduce to the same point of `E/𝔽ₚ`
(`red_p P = red_p Q`) but are distinct over `ℚ`: the reduction of their rational sum equals the
sum of their reductions. -/
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
    obtain rfl | hx12 := eq_or_ne x₁ x₂
    · -- `Q = -P`, so `P + Q = 0`, and the common reduced point is `2`-torsion.
      exact red_p_add_neg a₂ a₄ a₆ p hΔ h₁ h₂ hPQ hd1 rfl hYbar
    · -- `x₁ ≠ x₂` over `ℚ` but the reduced points coincide: the tangent-mod-`p` case, split on
      -- whether the common reduced point is `2`-torsion.
      by_cases hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
          (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)
      · exact red_p_add_tangent_two_torsion a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg
      · exact red_p_add_tangent_generic a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg

/-! ### The homomorphism -/

/-- Additivity of `red_p` on `some + some` when the two reduced representatives are proportional
mod `p` and the points are equal over `ℚ`: the reduced sum is an honest doubling. -/
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

/-- Additivity of `red_p` on `some + some` in the tangent-mod-`p` case: the reduced
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
`(curve …).toAffine.Point →+ ((curveℤ …).map (Int.castRingHom (ZMod p))).toAffine.Point`. -/
@[simps]
noncomputable def redHom (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point where
  toFun := red_p a₂ a₄ a₆ p hΔ
  map_zero' := red_p_zero a₂ a₄ a₆ p hΔ
  map_add' := red_p_map_add a₂ a₄ a₆ p hΔ

end ECCompute
