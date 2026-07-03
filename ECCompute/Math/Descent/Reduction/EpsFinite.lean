/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Math.Descent.PsiBase
import Mathlib.Algebra.Field.ZMod

/-!
# The finite-field descent character `εp_finite` and its additivity (T1d, chunk C4)

For a good prime `p` and a root `θ ∈ 𝔽ₚ` of `f = x³ + a₂x² + a₄x + a₆`, Cremona's descent
character on the reduced curve `E/𝔽ₚ` is

  `εp_finite θ : E(𝔽ₚ) → ZMod 2`,   `εp_finite θ O = 0`,
  `εp_finite θ (X, Y) = ψ_p(f'(θ))`   if `X = θ`,   `ψ_p(X − θ)`   otherwise,

where `ψ_p` is the Legendre symbol pushed into `(ZMod 2, +)`.  This file proves that
`εp_finite θ` is **additive**, packaged as `εpHom : E(𝔽ₚ) →+ ZMod 2`.  Vanishing on `2·E(𝔽ₚ)`
is then automatic (the target is `ZMod 2`).

The proof is the pure-`𝔽ₚ` analogue of `ECCompute.lambda_map_add_of_good` and
`ECCompute.lambda_double_of_good`, with the affine coordinates `X, Y` used *directly* (no
`Rat.cast`, no denominator side conditions), so it is strictly shorter than the `ℚ` versions.
The generic secant uses `vieta_of_roots` + `prod_sub_theta_eq_lineSq` and the arithmetic of
`ψ_p` on the nonzero factors, with the three `Xᵢ = θ` sub-cases handled by `fderiv_eq_prod`
and `fderiv_ne_zero`; doubling uses `vieta_of_double_root`; the trivial cases (`P = −Q`, a
summand `O`) come from the affine group law over `ZMod p`.

## Main declarations

* `ECCompute.reducedCurve` — the reduced Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over
  `ZMod p`.
* `ECCompute.εp_finite` — the finite-field descent character `E(𝔽ₚ) → ZMod 2`.
* `ECCompute.εp_finite_map_add` — additivity of `εp_finite`.
* `ECCompute.εpHom` — `εp_finite` packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace ECCompute

open scoped Classical

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-- The reduced Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ZMod p`, i.e. the reduction
mod `p` of `ECCompute.curve`.  The coefficients are the mod-`p` reductions of the integers
`a₂, a₄, a₆`, and `a₁ = a₃ = 0`. -/
def reducedCurve : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := (a₂ : ZMod p)
  a₃ := 0
  a₄ := (a₄ : ZMod p)
  a₆ := (a₆ : ZMod p)

variable [Fact p.Prime]

/-- The finite-field descent character.  On `O` it is `0`; on an affine point `(X, Y)` it is
`ψ_p(f'(θ))` in the tangent case `X = θ` and `ψ_p(X − θ)` otherwise. -/
noncomputable def εp_finite (θ : ZMod p) :
    (reducedCurve a₂ a₄ a₆ p).toAffine.Point → ZMod 2
  | .zero => 0
  | .some X _ _ => if X = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (X - θ)

@[simp]
theorem εp_finite_zero (θ : ZMod p) :
    εp_finite a₂ a₄ a₆ p θ (0 : (reducedCurve a₂ a₄ a₆ p).toAffine.Point) = 0 :=
  rfl

theorem εp_finite_some (θ : ZMod p) {X Y : ZMod p}
    (h : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular X Y) :
    εp_finite a₂ a₄ a₆ p θ (.some X Y h)
      = if X = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (X - θ) :=
  rfl

variable {a₂ a₄ a₆ p}
variable {θ : ZMod p}

/-- `εp_finite` on an affine point depends only on its `x`-coordinate: two points with equal `x`
have equal `εp_finite`. -/
theorem εp_x_indep {x₁ y₁ x₂ y₂ : ZMod p}
    {h₁ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁}
    {h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) :
    εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = εp_finite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl

/-- **Additivity of `εp_finite`, secant case.**  When `P = (x₁, y₁)` and `Q = (x₂, y₂)` have
distinct `x`-coordinates over `𝔽ₚ`, the collinearity square `(x₁ − θ)(x₂ − θ)(x₃ − θ)` is a
square, so `ψ_p` is additive on the nonzero factors; the three `2`-torsion sub-cases `xᵢ = θ`
replace the vanishing factor by `f'(θ) ≠ 0` via `fderiv_eq_prod`. -/
theorem εp_finite_map_add_of_X_ne (h : DescentHyp a₂ a₄ a₆ p θ)
    {x₁ y₁ x₂ y₂ : ZMod p}
    (h₁ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂)
    (hne : x₁ ≠ x₂) :
    εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) + εp_finite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  have hp2 : p ≠ 2 := fun hp => h.ne_six (hp ▸ ⟨3, rfl⟩)
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne]
  simp only [εp_finite_some]
  set ℓ := (reducedCurve a₂ a₄ a₆ p).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set X₃ := (reducedCurve a₂ a₄ a₆ p).toAffine.addX x₁ x₂ ℓ with hX3def
  have hdiff : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hℓmul : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hdiff]
  set m : ZMod p := y₁ - ℓ * x₁ with hmb
  have hm1 : ℓ * x₁ + m = y₁ := by rw [hmb]; ring
  have hm2 : ℓ * x₂ + m = y₂ := by rw [hmb]; linear_combination -hℓmul
  have hpt1 : (ℓ * x₁ + m) ^ 2
      = x₁ ^ 3 + (a₂ : ZMod p) * x₁ ^ 2 + (a₄ : ZMod p) * x₁ + (a₆ : ZMod p) := by
    rw [hm1]
    have := (WeierstrassCurve.Affine.equation_iff
      (W := (reducedCurve a₂ a₄ a₆ p).toAffine) x₁ y₁).mp h₁.1
    simpa [reducedCurve] using this
  have hpt2 : (ℓ * x₂ + m) ^ 2
      = x₂ ^ 3 + (a₂ : ZMod p) * x₂ ^ 2 + (a₄ : ZMod p) * x₂ + (a₆ : ZMod p) := by
    rw [hm2]
    have := (WeierstrassCurve.Affine.equation_iff
      (W := (reducedCurve a₂ a₄ a₆ p).toAffine) x₂ y₂).mp h₂.1
    simpa [reducedCurve] using this
  have hx3 : X₃ = ℓ ^ 2 - (a₂ : ZMod p) - x₁ - x₂ := by
    rw [hX3def]; simp only [WeierstrassCurve.Affine.addX, reducedCurve]; ring
  have hθroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    have := h.root; simpa [fval] using this
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m
    x₁ x₂ X₃ hne hx3 hpt1 hpt2
  have hprod : (x₁ - θ) * (x₂ - θ) * (X₃ - θ) = (ℓ * θ + m) ^ 2 :=
    prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₁ x₂ X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot
  have hfd_ne : fderiv a₂ a₄ a₆ p θ ≠ 0 := fderiv_ne_zero h
  have hfd1 : x₁ = θ → fderiv a₂ a₄ a₆ p θ = (x₂ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₁ x₂ X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot hc
  have hfd2 : x₂ = θ → fderiv a₂ a₄ a₆ p θ = (x₁ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₂ x₁ X₃ θ
      (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
      hθroot hc
  have hfd3 : X₃ = θ → fderiv a₂ a₄ a₆ p θ = (x₁ - θ) * (x₂ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m X₃ x₁ x₂ θ
      (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
      hθroot hc
  have hz : ∀ a b : ZMod 2, a + b + a = b := by decide
  have hz' : ∀ a b : ZMod 2, b = a + (a + b) := by decide
  have hzero : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by decide
  by_cases c1 : x₁ = θ
  · have hX2ne : x₂ ≠ θ := fun hc => hne (c1.trans hc.symm)
    have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd1 c1, hc]; ring)
    rw [if_neg hX3ne, if_pos c1, if_neg hX2ne, hfd1 c1,
      psi_mul h.prime hp2 (sub_ne_zero.mpr hX2ne) (sub_ne_zero.mpr hX3ne)]
    exact (hz _ _).symm
  by_cases c2 : x₂ = θ
  · have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd2 c2, hc]; ring)
    rw [if_neg hX3ne, if_neg c1, if_pos c2, hfd2 c2,
      psi_mul h.prime hp2 (sub_ne_zero.mpr c1) (sub_ne_zero.mpr hX3ne)]
    exact hz' _ _
  by_cases c3 : X₃ = θ
  · rw [if_pos c3, if_neg c1, if_neg c2, hfd3 c3,
      psi_mul h.prime hp2 (sub_ne_zero.mpr c1) (sub_ne_zero.mpr c2)]
  · have hs1 : x₁ - θ ≠ 0 := sub_ne_zero.mpr c1
    have hs2 : x₂ - θ ≠ 0 := sub_ne_zero.mpr c2
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((x₁ - θ) * (x₂ - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
    rw [psi_mul h.prime hp2 (mul_ne_zero hs1 hs2) hs3, psi_mul h.prime hp2 hs1 hs2] at hpm
    rw [if_neg c3, if_neg c1, if_neg c2]
    exact hzero _ _ _ hpm

/-- **Additivity of `εp_finite`, doubling case.**  If `P = (x, y)` is not `2`-torsion (`y ≠ 0`),
then `εp_finite` vanishes on `2P`: the collinear triple is `x, x, x₃` with the tangent slope
`ℓ = f'(x)/(2y)`, so the double-root Vieta relations make `(x − θ)²(x₃ − θ)` a square. -/
theorem εp_finite_double (h : DescentHyp a₂ a₄ a₆ p θ) {x y : ZMod p}
    (hP : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x y) (hy0 : y ≠ 0) :
    εp_finite a₂ a₄ a₆ p θ (.some x y hP + .some x y hP) = 0 := by
  have hp2 : p ≠ 2 := fun hp => h.ne_six (hp ▸ ⟨3, rfl⟩)
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hd)
  have h2y : (2 : ZMod p) * y ≠ 0 := mul_ne_zero h2 hy0
  have hneg : (reducedCurve a₂ a₄ a₆ p).toAffine.negY x y = -y := by
    simp [WeierstrassCurve.Affine.negY, reducedCurve]
  have hyne : y ≠ (reducedCurve a₂ a₄ a₆ p).toAffine.negY x y := by
    rw [hneg]; intro hh
    have h2yz : (2 : ZMod p) * y = 0 := by linear_combination hh
    exact hy0 ((mul_eq_zero.mp h2yz).resolve_left h2)
  have hcurve : y ^ 2
      = x ^ 3 + (a₂ : ZMod p) * x ^ 2 + (a₄ : ZMod p) * x + (a₆ : ZMod p) := by
    have := (WeierstrassCurve.Affine.equation_iff
      (W := (reducedCurve a₂ a₄ a₆ p).toAffine) x y).mp hP.1
    simpa [reducedCurve] using this
  have hθroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    have := h.root; simpa [fval] using this
  have hXθ : x ≠ θ := by
    intro hc; apply hy0
    have hYsq : y ^ 2 = 0 := by rw [hcurve, hc]; exact hθroot
    exact pow_eq_zero_iff (by norm_num) |>.mp hYsq
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne]
  simp only [εp_finite_some]
  set ℓ := (reducedCurve a₂ a₄ a₆ p).toAffine.slope x x y y with hℓdef
  set X₃ := (reducedCurve a₂ a₄ a₆ p).toAffine.addX x x ℓ with hX3def
  have hℓ : ℓ * (2 * y) = 3 * x ^ 2 + 2 * (a₂ : ZMod p) * x + (a₄ : ZMod p) := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, hneg, show y - -y = 2 * y by ring]
    simp only [reducedCurve]
    rw [div_mul_cancel₀ _ h2y]; ring
  set m : ZMod p := y - ℓ * x with hmb
  have hm : ℓ * x + m = y := by rw [hmb]; ring
  have hpt : (ℓ * x + m) ^ 2
      = x ^ 3 + (a₂ : ZMod p) * x ^ 2 + (a₄ : ZMod p) * x + (a₆ : ZMod p) := by
    rw [hm]; exact hcurve
  have htan : 3 * x ^ 2 + 2 * (a₂ : ZMod p) * x + (a₄ : ZMod p) = 2 * ℓ * (ℓ * x + m) := by
    rw [hm]; linear_combination -hℓ
  have hx3 : X₃ = ℓ ^ 2 - (a₂ : ZMod p) - 2 * x := by
    rw [hX3def]; simp only [WeierstrassCurve.Affine.addX, reducedCurve]; ring
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_double_root (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p)
    ℓ m x X₃ hpt htan hx3
  have hprod : (x - θ) * (x - θ) * (X₃ - θ) = (ℓ * θ + m) ^ 2 :=
    prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x x X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot
  by_cases c3 : X₃ = θ
  · rw [if_pos c3]
    have hfd : fderiv a₂ a₄ a₆ p θ = (x - θ) * (x - θ) := by
      have := fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m X₃ x x θ
        (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
        hθroot c3
      simpa [fderiv] using this
    rw [hfd]; exact psi_of_isSquare ⟨x - θ, by ring⟩
  · rw [if_neg c3]
    have hs : x - θ ≠ 0 := sub_ne_zero.mpr hXθ
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((x - θ) * (x - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
    rw [psi_mul h.prime hp2 (mul_ne_zero hs hs) hs3, psi_mul h.prime hp2 hs hs] at hpm
    have hfin : ∀ a b : ZMod 2, a + a + b = 0 → b = 0 := by decide
    exact hfin _ _ hpm

/-- **Additivity of `εp_finite`.**  The finite-field descent character is a homomorphism
`(E(𝔽ₚ), +) → (ZMod 2, +)`.  The trivial cases (`P = O`, `Q = O`, `P = −Q`) use the affine
group law; the `x₁ = x₂` case reduces to doubling (`εp_finite_double`), and `x₁ ≠ x₂` to the
secant case (`εp_finite_map_add_of_X_ne`). -/
theorem εp_finite_map_add (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (reducedCurve a₂ a₄ a₆ p).toAffine.Point) :
    εp_finite a₂ a₄ a₆ p θ (P + Q)
      = εp_finite a₂ a₄ a₆ p θ P + εp_finite a₂ a₄ a₆ p θ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Affine.Point.zero_def, zero_add, εp_finite_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Affine.Point.zero_def, add_zero, εp_finite_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (reducedCurve a₂ a₄ a₆ p).toAffine.negY x₂ y₂
  · -- `Q = -P`: the sum is `O`, and both summands share the `x`-coordinate, so `εpP + εpQ = 0`.
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2, εp_finite_zero,
      εp_x_indep (h₁ := h₁) (h₂ := h₂) hxy.1, ← two_mul, show (2 : ZMod 2) = 0 from by decide,
      zero_mul]
  · by_cases hne : x₁ = x₂
    · -- Doubling: `x₁ = x₂` forces `y₁ = y₂` (not the `-P` case), so `P = Q`; `εp(2P) = 0`.
      have hynegY : (reducedCurve a₂ a₄ a₆ p).toAffine.negY x₂ y₂ = -y₂ := by
        simp [WeierstrassCurve.Affine.negY, reducedCurve]
      have hyne' : y₁ ≠ -y₂ := fun hcon => hxy ⟨hne, by rw [hynegY]; exact hcon⟩
      have hy2eq : y₁ ^ 2 = y₂ ^ 2 := by
        have e1 : y₁ ^ 2
            = x₁ ^ 3 + (a₂ : ZMod p) * x₁ ^ 2 + (a₄ : ZMod p) * x₁ + (a₆ : ZMod p) := by
          have := (WeierstrassCurve.Affine.equation_iff
            (W := (reducedCurve a₂ a₄ a₆ p).toAffine) x₁ y₁).mp h₁.1
          simpa [reducedCurve] using this
        have e2 : y₂ ^ 2
            = x₂ ^ 3 + (a₂ : ZMod p) * x₂ ^ 2 + (a₄ : ZMod p) * x₂ + (a₆ : ZMod p) := by
          have := (WeierstrassCurve.Affine.equation_iff
            (W := (reducedCurve a₂ a₄ a₆ p).toAffine) x₂ y₂).mp h₂.1
          simpa [reducedCurve] using this
        rw [e1, e2, hne]
      have hy1ne0 : y₁ ≠ 0 := by
        intro h0
        have hy2z : y₂ = 0 := by
          have : y₂ ^ 2 = 0 := by rw [← hy2eq, h0]; ring
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        exact hyne' (by rw [h0, hy2z, neg_zero])
      have hyeq : y₁ = y₂ := by
        have hfac : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination hy2eq
        rcases mul_eq_zero.mp hfac with hh | hh
        · exact sub_eq_zero.mp hh
        · exact absurd (by linear_combination hh : y₁ = -y₂) hyne'
      subst hne; subst hyeq
      rw [show (Affine.Point.some x₁ y₁ h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Point)
          = Affine.Point.some x₁ y₁ h₁ from rfl, ← two_mul,
        show (2 : ZMod 2) = 0 from by decide, zero_mul]
      exact εp_finite_double h h₁ hy1ne0
    · -- Secant: `x₁ ≠ x₂`.
      exact εp_finite_map_add_of_X_ne h h₁ h₂ hne

/-- The finite-field descent character `εp_finite θ` as an `AddMonoidHom E(𝔽ₚ) → ZMod 2`. -/
noncomputable def εpHom (h : DescentHyp a₂ a₄ a₆ p θ) :
    (reducedCurve a₂ a₄ a₆ p).toAffine.Point →+ ZMod 2 where
  toFun := εp_finite a₂ a₄ a₆ p θ
  map_zero' := εp_finite_zero a₂ a₄ a₆ p θ
  map_add' := εp_finite_map_add h

@[simp]
theorem εpHom_apply (h : DescentHyp a₂ a₄ a₆ p θ)
    (P : (reducedCurve a₂ a₄ a₆ p).toAffine.Point) :
    εpHom h P = εp_finite a₂ a₄ a₆ p θ P :=
  rfl

/-- **`εp_finite` vanishes on `2·E(𝔽ₚ)`.**  Immediate from being a homomorphism into `ZMod 2`. -/
theorem εpHom_two_nsmul (h : DescentHyp a₂ a₄ a₆ p θ)
    (P : (reducedCurve a₂ a₄ a₆ p).toAffine.Point) :
    εpHom h (2 • P) = 0 := by
  rw [two_nsmul, map_add, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

end ECCompute
