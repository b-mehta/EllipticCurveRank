/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.PsiBase
import ECCompute.ForMathlib.WeierstrassCurveAffine
import Mathlib.Algebra.Field.ZMod

/-!
# The finite-field descent character `εp_finite` and its additivity

For a good prime `p` and a root `θ ∈ 𝔽ₚ` of `f = x³ + a₂x² + a₄x + a₆`, Cremona's descent
character on the reduced curve `E/𝔽ₚ` is

  `εp_finite θ : E(𝔽ₚ) → ZMod 2`,   `εp_finite θ O = 0`,
  `εp_finite θ (X, Y) = ψ_p(f'(θ))`   if `X = θ`,   `ψ_p(X - θ)`   otherwise,

where `ψ_p` is the Legendre symbol pushed into `(ZMod 2, +)`.  This file proves that
`εp_finite θ` is additive, packaged as `εpHom : E(𝔽ₚ) →+ ZMod 2`; vanishing on `2·E(𝔽ₚ)`
is then automatic.

## Main declarations

* `ECCompute.reducedCurve`: the reduced Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over
  `ZMod p`.
* `ECCompute.εp_finite`: the finite-field descent character `E(𝔽ₚ) → ZMod 2`.
* `ECCompute.εp_finite_map_add`: additivity of `εp_finite`.
* `ECCompute.εpHom`: `εp_finite` packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace ECCompute

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
`ψ_p(f'(θ))` in the tangent case `X = θ` and `ψ_p(X - θ)` otherwise. -/
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

/-- A point `(X, Y)` on the reduced curve satisfies the Weierstrass equation in expanded form. -/
private theorem reducedCurve_equation {X Y : ZMod p}
    (h : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular X Y) :
    Y ^ 2 = X ^ 3 + (a₂ : ZMod p) * X ^ 2 + (a₄ : ZMod p) * X + (a₆ : ZMod p) := by
  have := (WeierstrassCurve.Affine.equation_iff
    (W := (reducedCurve a₂ a₄ a₆ p).toAffine) X Y).mp h.1
  simpa [reducedCurve] using this

omit [Fact p.Prime] in
/-- `p ≠ 2` under the descent hypotheses (from `p ∤ 6`). -/
private theorem DescentHyp.ne_two (h : DescentHyp a₂ a₄ a₆ p θ) : p ≠ 2 :=
  fun hp => h.ne_six (hp ▸ ⟨3, rfl⟩)

/-- The root hypothesis `f(θ) = 0` in expanded form. -/
private theorem DescentHyp.root' (h : DescentHyp a₂ a₄ a₆ p θ) :
    θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
  simpa [fval] using h.root

/-- On the reduced curve (where `a₁ = a₃ = 0`) the negation `negY` is just `-y`. -/
private theorem reducedCurve_negY (x y : ZMod p) :
    (reducedCurve a₂ a₄ a₆ p).toAffine.negY x y = -y :=
  WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl x y

/-- `εp_finite` on an affine point depends only on its `x`-coordinate. -/
theorem εp_x_indep {x₁ y₁ x₂ y₂ : ZMod p}
    {h₁ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁}
    {h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) :
    εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = εp_finite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl

/-- The descent-character combination for a collinear triple `x₁, x₂, X₃` (with `x₁ ≠ x₂`)
whose Vieta relations for the secant line `y = ℓx + m` are given: the value at the third root
`X₃` equals the sum of the values at `x₁` and `x₂`.  The `𝔽ₚ`-arithmetic core of the secant
additivity, split off from the group-law setup in `εp_finite_map_add_of_X_ne`. -/
private theorem εp_sum_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m x₁ x₂ X₃ : ZMod p}
    (hne : x₁ ≠ x₂)
    (hσ₁ : x₁ + x₂ + X₃ = ℓ ^ 2 - (a₂ : ZMod p))
    (hσ₂ : x₁ * x₂ + x₁ * X₃ + x₂ * X₃ = (a₄ : ZMod p) - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * X₃ = m ^ 2 - (a₆ : ZMod p)) :
    (if X₃ = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (X₃ - θ))
      = (if x₁ = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (x₁ - θ))
        + (if x₂ = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (x₂ - θ)) := by
  have hθroot := h.root'
  have hfd_ne : fderiv a₂ a₄ a₆ p θ ≠ 0 := fderiv_ne_zero h
  have hfd1 : x₁ = θ → fderiv a₂ a₄ a₆ p θ = (x₂ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₁ x₂ X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot hc
  have hfd2 : x₂ = θ → fderiv a₂ a₄ a₆ p θ = (x₁ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₂ x₁ X₃ θ
      (by grind) (by grind) (by grind)
      hθroot hc
  have hfd3 : X₃ = θ → fderiv a₂ a₄ a₆ p θ = (x₁ - θ) * (x₂ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m X₃ x₁ x₂ θ
      (by grind) (by grind) (by grind)
      hθroot hc
  by_cases c1 : x₁ = θ
  · have hX2ne : x₂ ≠ θ := fun hc => hne (c1.trans hc.symm)
    have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd1 c1, hc]; grind)
    rw [if_neg hX3ne, if_pos c1, if_neg hX2ne, hfd1 c1,
      psi_mul h.prime (sub_ne_zero.mpr hX2ne) (sub_ne_zero.mpr hX3ne)]
    grind
  by_cases c2 : x₂ = θ
  · have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd2 c2, hc]; grind)
    rw [if_neg hX3ne, if_neg c1, if_pos c2, hfd2 c2,
      psi_mul h.prime (sub_ne_zero.mpr c1) (sub_ne_zero.mpr hX3ne)]
    grind
  by_cases c3 : X₃ = θ
  · rw [if_pos c3, if_neg c1, if_neg c2, hfd3 c3,
      psi_mul h.prime (sub_ne_zero.mpr c1) (sub_ne_zero.mpr c2)]
  · rw [if_neg c3, if_neg c1, if_neg c2]
    have := psi_collinear h.prime hσ₁ hσ₂ hσ₃ h.root c1 c2 c3
    grind

/-- Additivity of `εp_finite` in the secant case: `P = (x₁, y₁)` and `Q = (x₂, y₂)` have
distinct `x`-coordinates over `𝔽ₚ`. -/
theorem εp_finite_map_add_of_X_ne (h : DescentHyp a₂ a₄ a₆ p θ)
    {x₁ y₁ x₂ y₂ : ZMod p}
    (h₁ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂)
    (hne : x₁ ≠ x₂) :
    εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = εp_finite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) + εp_finite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne]
  simp only [εp_finite_some]
  set ℓ := (reducedCurve a₂ a₄ a₆ p).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set X₃ := (reducedCurve a₂ a₄ a₆ p).toAffine.addX x₁ x₂ ℓ with hX3def
  have hdiff : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hℓmul : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hdiff]
  set m : ZMod p := y₁ - ℓ * x₁ with hmb
  have hm1 : ℓ * x₁ + m = y₁ := by grind
  have hm2 : ℓ * x₂ + m = y₂ := by grind
  have hpt1 : (ℓ * x₁ + m) ^ 2
      = x₁ ^ 3 + (a₂ : ZMod p) * x₁ ^ 2 + (a₄ : ZMod p) * x₁ + (a₆ : ZMod p) := by
    rw [hm1]; exact reducedCurve_equation h₁
  have hpt2 : (ℓ * x₂ + m) ^ 2
      = x₂ ^ 3 + (a₂ : ZMod p) * x₂ ^ 2 + (a₄ : ZMod p) * x₂ + (a₆ : ZMod p) := by
    rw [hm2]; exact reducedCurve_equation h₂
  have hx3 : X₃ = ℓ ^ 2 - (a₂ : ZMod p) - x₁ - x₂ := by
    rw [hX3def]; grind [WeierstrassCurve.Affine.addX, reducedCurve]
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m
    x₁ x₂ X₃ hne hx3 hpt1 hpt2
  exact εp_sum_of_vieta h hne hσ₁ hσ₂ hσ₃

/-- The descent character vanishes at the double point of a tangent line: given the Vieta
relations for the double-root triple `x, x, X₃` at a root `θ ≠ x`, the value at `X₃` is `0`.
The `𝔽ₚ`-arithmetic core of the doubling case, split off from the group-law setup in
`εp_finite_double`. -/
private theorem εp_double_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m x X₃ : ZMod p}
    (hXθ : x ≠ θ)
    (hσ₁ : x + x + X₃ = ℓ ^ 2 - (a₂ : ZMod p))
    (hσ₂ : x * x + x * X₃ + x * X₃ = (a₄ : ZMod p) - 2 * ℓ * m)
    (hσ₃ : x * x * X₃ = m ^ 2 - (a₆ : ZMod p)) :
    (if X₃ = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (X₃ - θ)) = 0 := by
  have hθroot := h.root'
  have hprod : (x - θ) * (x - θ) * (X₃ - θ) = (ℓ * θ + m) ^ 2 :=
    prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x x X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot
  by_cases c3 : X₃ = θ
  · rw [if_pos c3]
    have hfd : fderiv a₂ a₄ a₆ p θ = (x - θ) * (x - θ) :=
      fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m X₃ x x θ
        (by grind) (by grind) (by grind)
        hθroot c3
    rw [hfd]
    exact psi_of_isSquare ⟨x - θ, by ring⟩
  · rw [if_neg c3]
    have hs : x - θ ≠ 0 := sub_ne_zero.mpr hXθ
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((x - θ) * (x - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
    rw [psi_mul h.prime (mul_ne_zero hs hs) hs3, psi_mul h.prime hs hs,
      CharTwo.add_self_eq_zero, zero_add] at hpm
    exact hpm

/-- Additivity of `εp_finite` in the doubling case: `εp_finite` vanishes on `2P` for a point
`P = (x, y)` that is not `2`-torsion (`y ≠ 0`). -/
theorem εp_finite_double (h : DescentHyp a₂ a₄ a₆ p θ) {x y : ZMod p}
    (hP : (reducedCurve a₂ a₄ a₆ p).toAffine.Nonsingular x y) (hy0 : y ≠ 0) :
    εp_finite a₂ a₄ a₆ p θ (.some x y hP + .some x y hP) = 0 := by
  have hp2 : p ≠ 2 := h.ne_two
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have h2y : (2 : ZMod p) * y ≠ 0 := mul_ne_zero h2 hy0
  have hneg := reducedCurve_negY (a₂ := a₂) (a₄ := a₄) (a₆ := a₆) x y
  have hyne : y ≠ (reducedCurve a₂ a₄ a₆ p).toAffine.negY x y := by
    grind
  have hcurve : y ^ 2
      = x ^ 3 + (a₂ : ZMod p) * x ^ 2 + (a₄ : ZMod p) * x + (a₆ : ZMod p) :=
    reducedCurve_equation hP
  have hθroot := h.root'
  have hXθ : x ≠ θ := by grind
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne]
  simp only [εp_finite_some]
  set ℓ := (reducedCurve a₂ a₄ a₆ p).toAffine.slope x x y y with hℓdef
  set X₃ := (reducedCurve a₂ a₄ a₆ p).toAffine.addX x x ℓ with hX3def
  have hℓ : ℓ * (2 * y) = 3 * x ^ 2 + 2 * (a₂ : ZMod p) * x + (a₄ : ZMod p) := by
    have hsub : y - -y = 2 * y := by ring
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, hneg, hsub]
    simp only [reducedCurve]
    rw [div_mul_cancel₀ _ h2y]
    ring
  set m : ZMod p := y - ℓ * x with hmb
  have hm : ℓ * x + m = y := by grind
  have hpt : (ℓ * x + m) ^ 2
      = x ^ 3 + (a₂ : ZMod p) * x ^ 2 + (a₄ : ZMod p) * x + (a₆ : ZMod p) := by
    rw [hm]; exact hcurve
  have htan : 3 * x ^ 2 + 2 * (a₂ : ZMod p) * x + (a₄ : ZMod p) = 2 * ℓ * (ℓ * x + m) := by
    grind
  have hx3 : X₃ = ℓ ^ 2 - (a₂ : ZMod p) - 2 * x := by
    rw [hX3def]; simp only [WeierstrassCurve.Affine.addX, reducedCurve]; ring
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_double_root (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p)
    ℓ m x X₃ hpt htan hx3
  exact εp_double_of_vieta h hXθ hσ₁ hσ₂ hσ₃

/-- Additivity of `εp_finite`: the finite-field descent character is a homomorphism
`(E(𝔽ₚ), +) → (ZMod 2, +)`. -/
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
      εp_x_indep (h₁ := h₁) (h₂ := h₂) hxy.1, CharTwo.add_self_eq_zero]
  · by_cases hne : x₁ = x₂
    · -- Doubling: `x₁ = x₂` forces `y₁ = y₂` (not the `-P` case), so `P = Q`; `εp(2P) = 0`.
      have hyne' : y₁ ≠ -y₂ := by grind [reducedCurve_negY]
      have hy2eq : y₁ ^ 2 = y₂ ^ 2 := by
        rw [reducedCurve_equation h₁, reducedCurve_equation h₂, hne]
      have hyeq : y₁ = y₂ := by grind
      have hy1ne0 : y₁ ≠ 0 := by grind
      subst hne hyeq
      have hpt : (Affine.Point.some x₁ y₁ h₂ : (reducedCurve a₂ a₄ a₆ p).toAffine.Point)
          = Affine.Point.some x₁ y₁ h₁ := rfl
      rw [hpt, CharTwo.add_self_eq_zero]
      exact εp_finite_double h h₁ hy1ne0
    · -- Secant: `x₁ ≠ x₂`.
      exact εp_finite_map_add_of_X_ne h h₁ h₂ hne

/-- The finite-field descent character `εp_finite θ` as an `AddMonoidHom E(𝔽ₚ) → ZMod 2`. -/
@[simps]
noncomputable def εpHom (h : DescentHyp a₂ a₄ a₆ p θ) :
    (reducedCurve a₂ a₄ a₆ p).toAffine.Point →+ ZMod 2 where
  toFun := εp_finite a₂ a₄ a₆ p θ
  map_zero' := εp_finite_zero a₂ a₄ a₆ p θ
  map_add' := εp_finite_map_add h

/-- `εp_finite` vanishes on `2·E(𝔽ₚ)`, immediate from being a homomorphism into `ZMod 2`. -/
theorem εpHom_two_nsmul (h : DescentHyp a₂ a₄ a₆ p θ)
    (P : (reducedCurve a₂ a₄ a₆ p).toAffine.Point) :
    εpHom h (2 • P) = 0 := by
  rw [map_nsmul, CharTwo.two_nsmul]

end ECCompute
