/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character
public import ECCompute.Theory.Model
public import Mathlib.Algebra.Field.ZMod
import ECCompute.ForMathlib.WeierstrassCurve

/-!
# The finite-field descent character `εpFinite` and its additivity

For a good prime `p` and a root `θ ∈ 𝔽ₚ` of `f = x³ + a₂x² + a₄x + a₆`, Cremona's descent
character on the reduced curve `E/𝔽ₚ` is

  `εpFinite θ : E(𝔽ₚ) → ZMod 2`,   `εpFinite θ O = 0`,
  `εpFinite θ (X, Y) = ψ_p(f'(θ))`   if `X = θ`,   `ψ_p(X - θ)`   otherwise,

where `ψ_p` is the Legendre symbol pushed into `(ZMod 2, +)`. This file proves that
`εpFinite θ` is additive, packaged as `εpHom : E(𝔽ₚ) →+ ZMod 2`; vanishing on `2·E(𝔽ₚ)`
is then automatic.

## Main declarations

* `ECCompute.εpFinite`: the finite-field descent character `E(𝔽ₚ) → ZMod 2`.
* `ECCompute.εpHom`: `εpFinite` packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

/-- The finite-field descent character. On `O` it is `0`; on an affine point `(X, Y)` it is
`ψ_p(f'(θ))` in the tangent case `X = θ` and `ψ_p(X - θ)` otherwise. -/
@[expose]
public noncomputable def εpFinite (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point → ZMod 2
  | .zero => 0
  | .some X _ _ => if X = θ then psi p (fderiv a₂ a₄ θ) else psi p (X - θ)

variable {θ : ZMod p} {x₁ y₁ x₂ y₂ : ZMod p}

@[simp]
theorem εpFinite_zero : εpFinite a₂ a₄ a₆ p θ 0 = 0 := rfl

public theorem εpFinite_some {X Y : ZMod p}
    (h : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular X Y) :
    εpFinite a₂ a₄ a₆ p θ (.some X Y h)
      = if X = θ then psi p (fderiv a₂ a₄ θ) else psi p (X - θ) :=
  rfl

/-- A point `(X, Y)` on the reduced curve satisfies the Weierstrass equation in expanded form. -/
theorem reduced_equation {X Y : ZMod p}
    (h : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular X Y) :
    Y ^ 2 = fval (R := ZMod p) a₂ a₄ a₆ X := by
  have := (Affine.equation_iff (W := (curveZMod a₂ a₄ a₆ p).toAffine) X Y).mp h.1
  simpa [map_curveℤ_zmod, fval] using this

/-- `p ≠ 2` under the descent hypotheses (from `p ∤ 6`). -/
theorem DescentHyp.ne_two (h : DescentHyp a₂ a₄ a₆ p θ) : p ≠ 2 := fun hp ↦ h.ne_six (hp ▸ ⟨3, rfl⟩)

/-- The root hypothesis `f(θ) = 0` in expanded form. -/
theorem DescentHyp.root' (h : DescentHyp a₂ a₄ a₆ p θ) : fval (R := ZMod p) a₂ a₄ a₆ θ = 0 :=
  h.root

/-- `εpFinite` on an affine point depends only on its `x`-coordinate. -/
theorem εp_x_indep
    (h₁ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = εpFinite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl

/-- For a collinear triple `x₁, x₂, X₃` with `x₁ ≠ x₂` and the given Vieta relations of the secant
line `y = ℓx + m`, the descent-character value at `X₃` equals the sum of the values at `x₁` and
`x₂`. -/
theorem εp_sum_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m X₃ : ZMod p} (hne : x₁ ≠ x₂)
    (hσ₁ : x₁ + x₂ + X₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * X₃ + x₂ * X₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * X₃ = m ^ 2 - a₆) :
    (if X₃ = θ then psi p (fderiv a₂ a₄ θ) else psi p (X₃ - θ))
      = (if x₁ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₁ - θ))
        + (if x₂ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₂ - θ)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hθroot := h.root'
  have hfd_ne : fderiv (a₂ : ZMod p) a₄ θ ≠ 0 := fderiv_ne_zero h
  have hfd1 : x₁ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₂ - θ) * (X₃ - θ) :=
    fderiv_eq_prod ℓ m hσ₁ hσ₂ hσ₃ hθroot
  have hfd2 : x₂ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₁ - θ) * (X₃ - θ) :=
    fderiv_eq_prod ℓ m (by grind) (by grind) (by grind) hθroot
  have hfd3 : X₃ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₁ - θ) * (x₂ - θ) :=
    fderiv_eq_prod ℓ m (by grind) (by grind) (by grind) hθroot
  obtain rfl | c1 := eq_or_ne x₁ θ
  · rw [if_neg (by grind), if_pos rfl, if_neg hne.symm, hfd1 rfl,
      psi_mul h.prime (by grind) (by grind)]
    grind
  obtain rfl | c2 := eq_or_ne x₂ θ
  · rw [if_neg (by grind), if_neg c1, if_pos rfl, hfd2 rfl, psi_mul h.prime (by grind) (by grind)]
    grind
  obtain rfl | c3 := eq_or_ne X₃ θ
  · rw [if_pos rfl, if_neg c1, if_neg c2, hfd3 rfl, psi_mul h.prime (by grind) (by grind)]
  · rw [if_neg c3, if_neg c1, if_neg c2]
    grind [psi_collinear h.prime hσ₁ hσ₂ hσ₃ h.root c1 c2 c3]

/-- Additivity of `εpFinite` in the secant case: `P = (x₁, y₁)` and `Q = (x₂, y₂)` have
distinct `x`-coordinates over `𝔽ₚ`. -/
theorem εpFinite_map_add_of_X_ne [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (h₁ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂) :
    εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) + εpFinite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  rw [Affine.Point.add_of_X_ne hne]
  simp only [εpFinite_some]
  set ℓ := (curveZMod a₂ a₄ a₆ p).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set X₃ := (curveZMod a₂ a₄ a₆ p).toAffine.addX x₁ x₂ ℓ with hX3def
  have hdiff : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hℓmul : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, Affine.slope_of_X_ne hne, div_mul_cancel₀ _ hdiff]
  set m : ZMod p := y₁ - ℓ * x₁ with hmb
  have hm1 : ℓ * x₁ + m = y₁ := by grind
  have hm2 : ℓ * x₂ + m = y₂ := by grind
  have hpt1 : (ℓ * x₁ + m) ^ 2 = fval (R := ZMod p) a₂ a₄ a₆ x₁ := by rw [hm1, reduced_equation h₁]
  have hpt2 : (ℓ * x₂ + m) ^ 2 = fval (R := ZMod p) a₂ a₄ a₆ x₂ := by rw [hm2, reduced_equation h₂]
  have hx3 : X₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by rw [hX3def]; simp [Affine.addX, map_curveℤ_zmod]
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots hne hx3 hpt1 hpt2
  exact εp_sum_of_vieta h hne hσ₁ hσ₂ hσ₃

/-- For the double-root triple `x, x, X₃` with the given Vieta relations at a root `θ ≠ x`, the
descent-character value at `X₃` is `0`. -/
theorem εp_double_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m x X₃ : ZMod p} (hXθ : x ≠ θ)
    (hσ₁ : x + x + X₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x * x + x * X₃ + x * X₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x * x * X₃ = m ^ 2 - a₆) :
    (if X₃ = θ then psi p (fderiv a₂ a₄ θ) else psi p (X₃ - θ)) = 0 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hθroot := h.root'
  have hprod : (x - θ) * (x - θ) * (X₃ - θ) = (ℓ * θ + m) ^ 2 :=
    prod_sub_theta_eq_lineSq hσ₁ hσ₂ hσ₃ hθroot
  obtain rfl | c3 := eq_or_ne X₃ θ
  · rw [if_pos rfl,
      fderiv_eq_prod ℓ m (x₂ := x) (x₃ := x) (by grind) (by grind) (by grind) hθroot rfl]
    exact psi_of_isSquare ⟨x - X₃, by ring⟩
  · rw [if_neg c3]
    have hs : x - θ ≠ 0 := sub_ne_zero.mpr hXθ
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((x - θ) * (x - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
    rwa [psi_mul h.prime (mul_ne_zero hs hs) hs3, psi_mul h.prime hs hs,
      CharTwo.add_self_eq_zero, zero_add] at hpm

/-- Additivity of `εpFinite` in the doubling case: `εpFinite` vanishes on `2P` for a point
`P = (x, y)` that is not `2`-torsion (`y ≠ 0`). -/
theorem εpFinite_double [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ) {x y : ZMod p}
    (hP : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y) (hy0 : y ≠ 0) :
    εpFinite a₂ a₄ a₆ p θ (.some x y hP + .some x y hP) = 0 := by
  have hp2 : p ≠ 2 := h.ne_two
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hyne : y ≠ (curveZMod a₂ a₄ a₆ p).toAffine.negY x y := by grind
  have hθroot := h.root'
  have hXθ : x ≠ θ := by grind [reduced_equation hP]
  rw [Affine.Point.add_self_of_Y_ne hyne]
  simp only [εpFinite_some]
  set ℓ := (curveZMod a₂ a₄ a₆ p).toAffine.slope x x y y with hℓdef
  set X₃ := (curveZMod a₂ a₄ a₆ p).toAffine.addX x x ℓ with hX3def
  have hℓ : ℓ * (2 * y) = 3 * x ^ 2 + 2 * a₂ * x + a₄ := by
    have hsub : y - -y = 2 * y := by grind
    rw [hℓdef, Affine.slope_of_Y_ne rfl hyne, reduced_negY, hsub]
    simp [map_curveℤ_zmod, field]
  set m : ZMod p := y - ℓ * x with hmb
  have hm : ℓ * x + m = y := by grind
  have hpt : (ℓ * x + m) ^ 2 = fval (R := ZMod p) a₂ a₄ a₆ x := by rw [hm, reduced_equation hP]
  have hx3 : X₃ = ℓ ^ 2 - a₂ - 2 * x := by rw [hX3def]; simp [Affine.addX, map_curveℤ_zmod]; ring
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_double_root hpt (by grind [fderiv]) hx3
  exact εp_double_of_vieta h hXθ hσ₁ hσ₂ hσ₃

/-- Additivity of `εpFinite`: the finite-field descent character is a homomorphism
`(E(𝔽ₚ), +) → (ZMod 2, +)`. -/
theorem εpFinite_map_add [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curveZMod a₂ a₄ a₆ p).toAffine.Point) :
    εpFinite a₂ a₄ a₆ p θ (P + Q) = εpFinite a₂ a₄ a₆ p θ P + εpFinite a₂ a₄ a₆ p θ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Affine.Point.zero_def, zero_add, εpFinite_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Affine.Point.zero_def, add_zero, εpFinite_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₂ y₂
  · -- `Q = -P`: the sum is `O`, and both summands share the `x`-coordinate, so `εpP + εpQ = 0`.
    rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, εpFinite_zero, εp_x_indep h₁ h₂ hxy.1,
      CharTwo.add_self_eq_zero]
  · obtain rfl | hne := eq_or_ne x₁ x₂
    · -- Doubling: `x₁ = x₂` forces `y₁ = y₂` (not the `-P` case), so `P = Q`; `εp(2P) = 0`.
      have hyne' : y₁ ≠ -y₂ := by grind
      have hy2eq : y₁ ^ 2 = y₂ ^ 2 := by rw [reduced_equation h₁, reduced_equation h₂]
      have hyeq : y₁ = y₂ := by grind
      have hy1ne0 : y₁ ≠ 0 := by grind
      subst hyeq
      have hpt : (Affine.Point.some x₁ y₁ h₂ :
          (curveZMod a₂ a₄ a₆ p).toAffine.Point) = Affine.Point.some x₁ y₁ h₁ := rfl
      rw [hpt, CharTwo.add_self_eq_zero]
      exact εpFinite_double h h₁ hy1ne0
    · -- Secant: `x₁ ≠ x₂`.
      exact εpFinite_map_add_of_X_ne h h₁ h₂ hne

/-- The finite-field descent character `εpFinite θ` as an `AddMonoidHom E(𝔽ₚ) → ZMod 2`. -/
@[expose, simps]
public noncomputable def εpHom [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point →+ ZMod 2 where
  toFun := εpFinite a₂ a₄ a₆ p θ
  map_zero' := by exact εpFinite_zero
  map_add' := by exact εpFinite_map_add h

end ECCompute
