/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.RedP
import ECCompute.Theory.Descent.Reduction.KernelClosure
import ECCompute.Theory.Descent.Reduction.ReducedSlope
import ECCompute.Theory.Descent.ReducedArith
import ECCompute.ForMathlib.WeierstrassCurveAffine
import ECCompute.ForMathlib.WeierstrassCurveProjective

/-!
# Additivity of the reduction map

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` of good reduction at a prime `p`, this file
proves that the reduction map `redP` on affine points is additive, and bundles it as an
`AddMonoidHom` `redHom`.

## Main declarations

* `ECCompute.redP_map_add`: additivity of `redP`.
* `ECCompute.redHom`: `redP` bundled as an `AddMonoidHom`.
-/

open WeierstrassCurve Projective

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]

/-! ### The fixed projective representative -/

/-- The fixed `ZMod p`-projective representative of an affine point used to compute `redP`:
`![0, 1, 0]` for the origin, and `ℤ → ZMod p` applied to the integer representative otherwise. -/
private noncomputable def repr :
    (curve a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h =>
      Int.castRingHom (ZMod p) ∘ trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose

/-- `repr` of an affine `some` point is `ℤ → ZMod p` applied to its integer representative. -/
private theorem repr_some_eq (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    repr a₂ a₄ a₆ p (.some x y h)
      = Int.castRingHom (ZMod p) ∘ trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose :=
  rfl

/-- `repr P` is a nonsingular representative on the reduced curve. -/
private theorem repr_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact nonsingular_zero
  | some x y h =>
      exact red_nonsingular a₂ a₄ a₆ p hΔ h
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2

/-- `redP` is `toAffine` of the fixed representative. -/
private theorem redP_eq_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    redP a₂ a₄ a₆ p hΔ P
      = Point.toAffine ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective
          (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact (Point.toAffine_zero).symm
  | some x y h => rfl

/-- Over `ℚ`, the affine point underlying the integer representative `trep x y w` is `(x, y)`. -/
private theorem toAffine_g_trep {x y : ℚ} {w : ℕ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ trep x y w)
      = .some x y h := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rw [trep_map_ℚ hden hden',
    Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (by positivity)),
    Point.toAffine_some ((nonsingular_some x y).mpr h)]

/-- An integer projective representative whose rational affine point is a `some` is nonsingular
over `ℚ` (the affine point of a singular representative is the origin). -/
private theorem nonsingular_of_toAffine_some {U : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hU : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U)
      = .some X Y hR) :
    (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) := by
  grind [Point.toAffine_of_singular, Affine.Point.some_ne_zero]

/-- If two integer projective representatives have the same (rational) affine point, then they are
proportional over `ℤ`, with the cross scalars given by each other's `Z`-coordinate. -/
private theorem int_smul_eq_of_toAffine_eq {S T : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curve a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hS : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ S)
      = .some X Y hR)
    (hT : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T)
      = .some X Y hR) :
    T 2 • S = S 2 • T := by
  have key : ∀ U : Fin 3 → ℤ,
      Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U)
        = .some X Y hR → (U 0 : ℚ) = X * U 2 ∧ (U 1 : ℚ) = Y * U 2 := by
    intro U hU
    have hg : ∀ i, (Int.castRingHom ℚ ∘ U) i = (U i : ℚ) := fun i ↦ by
      simp [Function.comp_apply]
    have hUz : (Int.castRingHom ℚ ∘ U) 2 ≠ 0 := by
      grind [Point.toAffine_of_Z_eq_zero, Affine.Point.some_ne_zero]
    have hns : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) :=
      nonsingular_of_toAffine_some a₂ a₄ a₆ hU
    rw [Point.toAffine_of_Z_ne_zero hns hUz, Affine.Point.some.injEq] at hU
    rw [hg] at hUz
    exact ⟨(div_eq_iff hUz).mp (hg 0 ▸ hU.1), (div_eq_iff hUz).mp (hg 1 ▸ hU.2)⟩
  obtain ⟨hS0, hS1⟩ := key S hS
  obtain ⟨hT0, hT1⟩ := key T hT
  funext i
  fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
  · have : ((T 2 * S 0 : ℤ) : ℚ) = ((S 2 * T 0 : ℤ) : ℚ) := by grind
    exact mod_cast this
  · have : ((T 2 * S 1 : ℤ) : ℚ) = ((S 2 * T 1 : ℤ) : ℚ) := by grind
    exact mod_cast this
  · exact mul_comm _ _

/-- Reduction is well-defined on classes: any integer projective representative `T` whose
rational affine point is `R` reduces mod `p` to a representative equivalent to `repr R`. -/
private theorem repr_equiv_of_toAffine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (R : (curve a₂ a₄ a₆).toAffine.Point) {T : Fin 3 → ℤ}
    (hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ T))
    (hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ T))
    (hTℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T) = R) :
    (repr a₂ a₄ a₆ p R) ≈ (Int.castRingHom (ZMod p) ∘ T) := by
  cases R with
  | zero =>
    have hTz : (Int.castRingHom ℚ ∘ T) 2 = 0 := by
      grind [Point.toAffine_of_Z_ne_zero, Affine.Point.some_ne_zero]
    have hTz' : T 2 = 0 := by simpa [Function.comp_apply] using hTz
    have hfTz : (Int.castRingHom (ZMod p) ∘ T) 2 = 0 := by simp [Function.comp_apply, hTz']
    exact Setoid.symm (equiv_zero_of_Z_eq_zero hnsp hfTz)
  | some X Y hR =>
    set w₃ := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose with hw₃
    have hd3 : X.den = w₃ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose_spec.1
    have hd3' : Y.den = w₃ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ hR).choose_spec.2
    have hStℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective
        (Int.castRingHom ℚ ∘ trep X Y w₃) = .some X Y hR :=
      toAffine_g_trep a₂ a₄ a₆ hR hd3 hd3'
    have hid : T 2 • trep X Y w₃ = trep X Y w₃ 2 • T :=
      int_smul_eq_of_toAffine_eq a₂ a₄ a₆ hStℚ hTℚ
    have hprop : (Int.castRingHom (ZMod p) ∘ T) 2 •
          (Int.castRingHom (ZMod p) ∘ trep X Y w₃)
        = (Int.castRingHom (ZMod p) ∘ trep X Y w₃) 2 • (Int.castRingHom (ZMod p) ∘ T) := by
      have h := congrArg (fun Q : Fin 3 → ℤ ↦ Int.castRingHom (ZMod p) ∘ Q) hid
      simpa only [comp_smul, Function.comp_apply] using h
    exact equiv_of_proportional (repr_nonsingular a₂ a₄ a₆ p hΔ (.some X Y hR)) hnsp
      hprop

/-- Common closing step for the doubling and secant cases of additivity: an integer
representative `V` whose reduction is the reduced sum (`hadd`) and whose rational value is the
rational sum of two nonsingular representatives `A`, `B` (`hgadd`) is equivalent mod `p` to `repr`
of the affine sum `toAffine A + toAffine B`. -/
private theorem sum_repr_equiv (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {V : Fin 3 → ℤ}
    {A B : Fin 3 → ℚ} (P Q : (curve a₂ a₄ a₆).toAffine.Point)
    (hnsA : (curve a₂ a₄ a₆).toProjective.Nonsingular A)
    (hnsB : (curve a₂ a₄ a₆).toProjective.Nonsingular B)
    (hgadd : Int.castRingHom ℚ ∘ V = (curve a₂ a₄ a₆).toProjective.add A B)
    (haffA : Point.toAffine (curve a₂ a₄ a₆).toProjective A = P)
    (haffB : Point.toAffine (curve a₂ a₄ a₆).toProjective B = Q)
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
      (repr a₂ a₄ a₆ p P) (repr a₂ a₄ a₆ p Q) = Int.castRingHom (ZMod p) ∘ V) :
    repr a₂ a₄ a₆ p (P + Q) ≈ (Int.castRingHom (ZMod p) ∘ V) := by
  have hnsp : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ V) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)
  have hnsq : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ V) := by
    rw [hgadd]; exact nonsingular_add hnsA hnsB
  have hTℚ : Point.toAffine (curve a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ V)
      = P + Q := by rw [hgadd, Point.toAffine_add hnsA hnsB, haffA, haffB]
  exact repr_equiv_of_toAffine a₂ a₄ a₆ p hΔ _ hnsp hnsq hTℚ

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

/-- Additivity of `redP` in the tangent-mod-`p` `2`-torsion sub-case: the shared reduced point
satisfies `Ȳ₁ = -Ȳ₁`, and both `redP (P + Q)` and `P̄ + P̄` are the origin. -/
private theorem redP_add_tangent_two_torsion (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : Rat.IsPIntegral p x₁) (hd2 : Rat.IsPIntegral p x₂)
    (hdy1 : Rat.IsPIntegral p y₁) (hdy2 : Rat.IsPIntegral p y₂)
    (hXbar : (x₁ : ZMod p) = (x₂ : ZMod p)) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p))
    (hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  rw [redP_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, Affine.Point.add_of_Y_eq rfl hYneg,
    Affine.Point.add_of_X_ne hne]
  apply redP_of_den_zero a₂ a₄ a₆ p hΔ
    (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left))
  intro hd3_s
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
        (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1).mpr
        (Rat.mem_padicInteger_iff.mp hd1))
  rw [WeierstrassCurve.Affine.nonsingular_iff, map_curveℤ_zmod] at hns
  simp only [zero_mul, sub_zero] at hns
  exact hns.2.elim (fun hfd_ne ↦ (Ne.symm hfd_ne) hfd) (fun hyne2 ↦ hyne2 hYeq)

/-- Tangent-mod-`p` additivity, genuine-tangent sub-case (`Ȳ₁ + Ȳ₂ ≠ 0`): the reduced sum
`redP (P + Q)` is the tangent doubling of the common reduced point `P̄`. Both reduced `x`- and
`y`-coordinates are matched against the doubling formulas via the reduced tangent identities. -/
private theorem redP_add_tangent_generic (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : Rat.IsPIntegral p x₁) (hd2 : Rat.IsPIntegral p x₂)
    (hdy1 : Rat.IsPIntegral p y₁) (hdy2 : Rat.IsPIntegral p y₂)
    (hXbar : (x₁ : ZMod p) = (x₂ : ZMod p)) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p))
    (hYneg : ¬ (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  have hslX : (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
    WeierstrassCurve.Affine.slope_of_X_ne hne
  set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂) with hℓdef
  have haddX : (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - (a₂ : ℚ) - x₁ - x₂ := by
    simp only [WeierstrassCurve.Affine.addX, curve]; grind
  have hy2 : (y₁ : ZMod p) + (y₂ : ZMod p) ≠ 0 := by grind
  have hℓden_s : Rat.IsPIntegral p ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) :=
    reduced_slope_den a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hy2
  have hℓden : Rat.IsPIntegral p ℓ := by rwa [← hslX]
  have hd3 : Rat.IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ) :=
    addX_den_ne a₂ a₄ a₆ p hℓden hd1 hd2 haddX
  have hd3_s : Rat.IsPIntegral p ((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)) := by rwa [hslX]
  obtain ⟨hS2, htan⟩ :=
    reduced_tangent_eqs a₂ a₄ a₆ p hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
  rw [hslX] at hS2 htan
  have h2Yne : (y₁ : ZMod p) + (y₁ : ZMod p) ≠ 0 := by grind
  have hℓd := reduced_slope_eq a₂ a₄ a₆ p hYneg h2Yne hXbar hYbar htan
  have hy3cast := addY_cast_eq a₂ a₄ a₆ p (x₂ := x₂) hℓden hd1 hdy1 hd3
  have hns3 := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left)
  grind [Affine.Point.add_of_X_ne, redP_of_den_ne, Affine.Point.add_of_Y_ne,
    Affine.Point.some.injEq, reduced_addX_eq, reduced_addY_eq]

/-- Additivity when both summands reduce to the origin (`p ∣ x₁.den`, `p ∣ x₂.den`): the sum also
reduces to the origin. Uses `den_addX_both_kernel`. -/
private theorem redP_add_kernel (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : ¬ Rat.IsPIntegral p x₁) (hd2 : ¬ Rat.IsPIntegral p x₂) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  have hz1 : (x₁.den : ZMod p) = 0 := by by_contra h; exact hd1 (Rat.mem_padicInteger_iff.mpr h)
  have hz2 : (x₂.den : ZMod p) = 0 := by by_contra h; exact hd2 (Rat.mem_padicInteger_iff.mpr h)
  obtain rfl | hx12 := eq_or_ne x₁ x₂
  · rw [Affine.Point.add_of_Y_eq rfl (y_eq_negY_of_X_eq a₂ a₄ a₆ h₁ h₂ rfl hPQ), redP_zero]
  · rw [Affine.Point.add_of_X_ne hx12]
    refine redP_of_den_zero a₂ a₄ a₆ p hΔ _ (fun hmem ↦ Rat.mem_padicInteger_iff.mp hmem ?_)
    exact den_addX_both_kernel a₂ a₄ a₆ p h₁.1 h₂.1 hx12 hz1 hz2

/-- Additivity when the reduced points coincide and `Q = -P` over `ℚ` (`x₁ = x₂`): then `P + Q = 0`
and the common reduced point is `2`-torsion, so `redP (P + Q) = 0 = P̄ + P̄`. -/
private theorem redP_add_neg (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : Rat.IsPIntegral p x₁) (hx12 : x₁ = x₂) (hYbar : (y₁ : ZMod p) = (y₂ : ZMod p)) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
  have hy : y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ := y_eq_negY_of_X_eq a₂ a₄ a₆ h₁ h₂ hx12 hPQ
  rw [Affine.Point.add_of_Y_eq hx12 hy, redP_zero, redP_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1]
  have hyneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
      (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p) := by
    have hny : (curve a₂ a₄ a₆).toAffine.negY x₂ y₂ = -y₂ :=
      Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl x₂ y₂
    have hcast : (y₁ : ZMod p) = -(y₂ : ZMod p) := by rw [hy, hny, Rat.cast_neg]
    grind
  rw [Affine.Point.add_of_Y_eq rfl hyneg]

/-- Additivity of `redP` when two affine points `P`, `Q` reduce to the same point of `E/𝔽ₚ`
(`redP P = redP Q`) but are distinct over `ℚ`: the reduction of their rational sum equals the
sum of their reductions. -/
private theorem redP_add_tangent (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hred : redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) = redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
  by_cases hd1 : Rat.IsPIntegral p x₁
  · -- `P` has good reduction; then so does `Q`, and they share reduced coordinates.
    have hd2 : Rat.IsPIntegral p x₂ := by
      grind [redP_of_den_ne, redP_of_den_zero, Affine.Point.some_ne_zero]
    have hdy1 : Rat.IsPIntegral p y₁ := ydenom_pIntegral h₁.1 hd1
    have hdy2 : Rat.IsPIntegral p y₂ := ydenom_pIntegral h₂.1 hd2
    rw [redP_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, redP_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
      Affine.Point.some.injEq] at hred
    obtain ⟨hXbar, hYbar⟩ := hred
    -- Rewrite `red Q` to `red P` throughout: the two reduced points coincide.
    have hQeqP : redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) := by
      rw [redP_of_den_ne a₂ a₄ a₆ p hΔ h₁ hd1, redP_of_den_ne a₂ a₄ a₆ p hΔ h₂ hd2,
        Affine.Point.some.injEq]
      exact ⟨hXbar.symm, hYbar.symm⟩
    rw [hQeqP]
    obtain rfl | hx12 := eq_or_ne x₁ x₂
    · -- `Q = -P`, so `P + Q = 0`, and the common reduced point is `2`-torsion.
      exact redP_add_neg a₂ a₄ a₆ p hΔ h₁ h₂ hPQ hd1 rfl hYbar
    · -- `x₁ ≠ x₂` over `ℚ` but the reduced points coincide: the tangent-mod-`p` case, split on
      -- whether the common reduced point is `2`-torsion.
      by_cases hYneg : (y₁ : ZMod p) = ((curveℤ a₂ a₄ a₆).map
          (Int.castRingHom (ZMod p))).toAffine.negY (x₁ : ZMod p) (y₁ : ZMod p)
      · exact redP_add_tangent_two_torsion a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg
      · exact redP_add_tangent_generic a₂ a₄ a₆ p hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2
          hXbar hYbar hYneg
  · -- `P → O`, hence (by `hred`) `Q → O` as well; the sum reduces to `O`.
    have hQ0 : redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) = 0 := by
      rw [← hred]; exact redP_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1
    have hd2 : ¬ Rat.IsPIntegral p x₂ := by
      grind [redP_of_den_ne, Affine.Point.some_ne_zero]
    rw [redP_of_den_zero a₂ a₄ a₆ p hΔ h₁ hd1, hQ0, add_zero]
    exact redP_add_kernel a₂ a₄ a₆ p hΔ h₁ h₂ hPQ hd1 hd2

/-! ### The homomorphism -/

/-- Additivity of `redP` on `some + some` when the two reduced representatives are proportional
mod `p` and the points are equal over `ℚ`: the reduced sum is an honest doubling. -/
private theorem redP_map_add_double (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘
      trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose))
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₁ y₁ h₁)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hgadd : Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁)
      = (curve a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁) := by
    rw [add_self, ← map_curveℤ_ℚ]
    exact (map_dblXYZ (Int.castRingHom ℚ) _).symm
  exact sum_repr_equiv a₂ a₄ a₆ p hΔ _ _ hns1 hns1 hgadd
    (toAffine_g_trep a₂ a₄ a₆ h₁ hden1 hden1')
    (toAffine_g_trep a₂ a₄ a₆ h₁ hden1 hden1') hadd

/-- Additivity of `redP` on `some + some` in the secant case (`¬ repr P ≈ repr Q` mod `p`): the
reduced sum is a secant, and the two representatives are also inequivalent over `ℚ`. -/
private theorem redP_map_add_secant (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘
      trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose))
    (hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘
      trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose))
    (heq : ¬ (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ
          (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)
          (trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  set w₂ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hden2 : x₂.den = w₂ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.1
  have hden2' : y₂.den = w₂ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.2
  have hℚne : ¬ (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁) ≈ (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂) := by
    intro hℚeq
    apply heq
    have hpt : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂ := by
      rw [← toAffine_g_trep a₂ a₄ a₆ h₁ hden1 hden1', ← toAffine_g_trep a₂ a₄ a₆ h₂ hden2 hden2']
      exact Point.toAffine_of_equiv hℚeq
    exact hpt ▸ Setoid.refl (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁))
  have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
          (trep x₂ y₂ w₂) := by
    rw [add_of_not_equiv heq, repr_some_eq, repr_some_eq]
    exact map_addXYZ (Int.castRingHom (ZMod p)) _ _
  have hgaddXYZ : (curve a₂ a₄ a₆).toProjective.addXYZ (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
        (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂)
      = Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
          (trep x₂ y₂ w₂) := by
    rw [← map_curveℤ_ℚ]; exact map_addXYZ (Int.castRingHom ℚ) _ _
  have hgadd : Int.castRingHom ℚ ∘ (curveℤ a₂ a₄ a₆).toProjective.addXYZ (trep x₁ y₁ w₁)
        (trep x₂ y₂ w₂)
      = (curve a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ trep x₂ y₂ w₂) := by
    rw [← hgaddXYZ]; exact (add_of_not_equiv hℚne).symm
  exact sum_repr_equiv a₂ a₄ a₆ p hΔ _ _ hns1 hns2 hgadd
    (toAffine_g_trep a₂ a₄ a₆ h₁ hden1 hden1') (toAffine_g_trep a₂ a₄ a₆ h₂ hden2 hden2') hadd

/-- Additivity of `redP` on `some + some` in the tangent-mod-`p` case: the reduced
representatives are proportional but the points differ over `ℚ`. The projective-class goal is
reduced to the affine additivity supplied by `redP_add_tangent`. -/
private theorem redP_map_add_tangent_case (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {x₁ y₁ x₂ y₂ : ℚ} (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (heq : (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂)))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
        (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) :
    repr a₂ a₄ a₆ p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
          (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose) := by
  have hred : redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) = redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
    rw [redP_eq_toAffine, redP_eq_toAffine]; exact Point.toAffine_of_equiv heq
  have hnspV : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ
        (trep x₁ y₁ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose)) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)
  refine equiv_of_toAffine_eq (repr_nonsingular a₂ a₄ a₆ p hΔ _) hnspV ?_
  rw [← redP_eq_toAffine a₂ a₄ a₆ p hΔ, ← hadd,
    Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _),
    ← redP_eq_toAffine a₂ a₄ a₆ p hΔ, ← redP_eq_toAffine a₂ a₄ a₆ p hΔ]
  exact redP_add_tangent a₂ a₄ a₆ p hΔ h₁ h₂ hred hPQ

/-- Additivity of the reduction map on two `some` points, reduced to a projective-class
equivalence and dispatched to the doubling, tangent-mod-`p` and secant sub-cases. -/
private theorem redP_map_add_some (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) :
    redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂) := by
  set w₁ := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose
  have hden1 : x₁.den = w₁ ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.1
  have hden1' : y₁.den = w₁ ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h₁).choose_spec.2
  have hns1 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ trep x₁ y₁ w₁) :=
    nonsingular_of_toAffine_some a₂ a₄ a₆ (toAffine_g_trep a₂ a₄ a₆ h₁ hden1 hden1')
  have hns2 : (curve a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘
      trep x₂ y₂ (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose) :=
    nonsingular_of_toAffine_some a₂ a₄ a₆ (toAffine_g_trep a₂ a₄ a₆ h₂
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.1
      (den_isSquare_of_nonsingular a₂ a₄ a₆ h₂).choose_spec.2)
  rw [redP_eq_toAffine, redP_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁),
    redP_eq_toAffine a₂ a₄ a₆ p hΔ (.some x₂ y₂ h₂),
    ← Point.toAffine_add (repr_nonsingular a₂ a₄ a₆ p hΔ _)
      (repr_nonsingular a₂ a₄ a₆ p hΔ _)]
  refine Point.toAffine_of_equiv ?_
  by_cases heq : (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) ≈ (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
  · -- `repr P ≈ repr Q` mod `p`: the reduced sum is a doubling of `repr P`.
    have hadd : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.add
          (repr a₂ a₄ a₆ p (.some x₁ y₁ h₁)) (repr a₂ a₄ a₆ p (.some x₂ y₂ h₂))
        = Int.castRingHom (ZMod p) ∘ (curveℤ a₂ a₄ a₆).toProjective.dblXYZ (trep x₁ y₁ w₁) := by
      rw [add_of_equiv heq, repr_some_eq]
      exact map_dblXYZ (Int.castRingHom (ZMod p)) _
    rw [hadd]
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curve a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂
    · rw [← hPQ] at hadd ⊢; exact redP_map_add_double a₂ a₄ a₆ p hΔ h₁ hns1 hadd
    · exact redP_map_add_tangent_case a₂ a₄ a₆ p hΔ h₁ h₂ heq hPQ hadd
  · rw [add_of_not_equiv heq, repr_some_eq, repr_some_eq,
      map_addXYZ (Int.castRingHom (ZMod p))]
    exact redP_map_add_secant a₂ a₄ a₆ p hΔ h₁ h₂ hns1 hns2 heq

/-- Additivity of the reduction map. -/
theorem redP_map_add (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    redP a₂ a₄ a₆ p hΔ (P + Q) = redP a₂ a₄ a₆ p hΔ P + redP a₂ a₄ a₆ p hΔ Q := by
  cases P with
  | zero =>
      change redP a₂ a₄ a₆ p hΔ (0 + Q) = redP a₂ a₄ a₆ p hΔ 0 + redP a₂ a₄ a₆ p hΔ Q
      rw [zero_add, redP_zero, zero_add]
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero =>
      change redP a₂ a₄ a₆ p hΔ (Affine.Point.some x₁ y₁ h₁ + 0)
        = redP a₂ a₄ a₆ p hΔ (.some x₁ y₁ h₁) + redP a₂ a₄ a₆ p hΔ 0
      rw [add_zero, redP_zero, add_zero]
  | some x₂ y₂ h₂ => exact redP_map_add_some a₂ a₄ a₆ p hΔ h₁ h₂

/-- The reduction map bundled as an additive homomorphism
`(curve …).toAffine.Point →+ ((curveℤ …).map (Int.castRingHom (ZMod p))).toAffine.Point`. -/
@[simps]
noncomputable def redHom (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point where
  toFun := redP a₂ a₄ a₆ p hΔ
  map_zero' := redP_zero a₂ a₄ a₆ p hΔ
  map_add' := redP_map_add a₂ a₄ a₆ p hΔ

end ECCompute
