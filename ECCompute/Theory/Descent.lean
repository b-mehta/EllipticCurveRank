/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.Hom
import ECCompute.Theory.Descent.Reduction.EpsFinite

/-!
# The descent character: additivity

This file assembles the additivity of the descent character `λ_{p,θ}` defined in
`ECCompute.Theory.Descent.Defs`. Additivity is obtained by factoring `λ` through the reduction map
`red_p : E(ℚ) → E(𝔽ₚ)` and the finite-field descent character `εp_finite`, both of which are
additive homomorphisms (see `ECCompute.Theory.Descent.Reduction.Hom` and
`ECCompute.Theory.Descent.Reduction.EpsFinite`).

## Main declarations

* `ECCompute.lambda_some_of_den_ne`, `ECCompute.lambda_some_of_den_zero`: the value of `λ` on an
  affine point, split on whether `p` divides the `x`-denominator.
* `ECCompute.redCharHom`: the composition `εp_finite θ ∘ red_p` as an `AddMonoidHom`.
* `ECCompute.lambda_eq_εp_red`: `λ` agrees pointwise with that composition.
* `ECCompute.lambda_map_add`: the trusted theorem, `λ` is additive.
* `ECCompute.lambdaHom`: `λ` packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### Reducing `λ` on an affine point to `ψ_p` of the reduced coordinate -/

section Reduce

variable {a₂ a₄ a₆ p}

/-- Reduction of `λ` on an affine point with `p ∤ x.den` to `ψ_p` of the reduced coordinate.

Writing `x.den = w²` (a square, from `den_isSquare_of_nonsingular`), the descent value
`α = x.num - θ·x.den = w²·(X - θ)`, so `ψ_p(α) = ψ_p(X - θ)` and the tangent branch `α = 0`
is exactly `X = θ`. -/
theorem lambda_some_of_den_ne [Fact p.Prime] {θ : ZMod p} {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    lambda a₂ a₄ a₆ p θ (.some x y h)
      = if xbar p x = θ then psi p (fderiv a₂ a₄ p θ) else psi p (xbar p x - θ) := by
  obtain ⟨w, hxden, _⟩ := den_isSquare_of_nonsingular a₂ a₄ a₆ h
  have hw : (w : ZMod p) ≠ 0 := by
    intro h0; apply hd; rw [hxden]; grind
  have halpha : (x.num : ZMod p) - θ * (x.den : ZMod p) = (w : ZMod p) ^ 2 * (xbar p x - θ) := by
    rw [num_eq_xbar_mul_den hd, hxden]; grind
  simp only [lambda]
  grind [psi_mul_sq]

/-- When `p ∣ x.den` the point reduces to `O` of `E/𝔽ₚ`, where `λ` vanishes. -/
theorem lambda_some_of_den_zero {θ : ZMod p} {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    lambda a₂ a₄ a₆ p θ (.some x y h) = 0 := by
  simp only [lambda, if_pos hd]

end Reduce

/-! ### The trusted theorem: additivity via the reduction factorization -/

/-- The descent character `λ_{p,θ}` presented as the composition `εp_finite θ ∘ red_p`, packaged
as an `AddMonoidHom E(ℚ) → ZMod 2`. -/
noncomputable def redCharHom [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 :=
  (εpHom h).comp (redHom a₂ a₄ a₆ p hΔ)

/-- On each point, `λ_{p,θ}` agrees with the reduction composition `εp_finite θ ∘ red_p`. -/
theorem lambda_eq_εp_red [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ P = redCharHom a₂ a₄ a₆ p h hΔ P := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, lambda_zero, map_zero]
  | some x y hns =>
    rw [redCharHom, AddMonoidHom.comp_apply, redHom_apply]
    by_cases hd : (x.den : ZMod p) = 0
    · rw [lambda_some_of_den_zero hns hd, red_p_of_den_zero a₂ a₄ a₆ p hΔ hns hd, map_zero]
    · rw [lambda_some_of_den_ne hns hd, red_p_of_den_ne a₂ a₄ a₆ p hΔ hns hd]
      simp only [εpHom_apply, εp_finite_some, xbar]
      rfl

/-- The descent character `λ_{p,θ}` is additive, i.e. a homomorphism `(E(ℚ), +) → (ZMod 2, +)`. -/
theorem lambda_map_add {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ (P + Q) = lambda a₂ a₄ a₆ p θ P + lambda a₂ a₄ a₆ p θ Q := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0 := by
    have hval : (curve a₂ a₄ a₆).Δ = ((curveℤ a₂ a₄ a₆).Δ : ℚ) := by
      rw [← baseChange_curveℤ_ℚ, baseChange, algebraMap_int_eq, map_Δ, eq_intCast]
    rw [← Rat.num_intCast (curveℤ a₂ a₄ a₆).Δ]
    grind
  simp only [lambda_eq_εp_red a₂ a₄ a₆ p h hΔ, map_add]

/-- The descent character `λ_{p,θ}` as an `AddMonoidHom E(ℚ) → ZMod 2`. -/
@[simps]
noncomputable def lambdaHom {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 where
  toFun := lambda a₂ a₄ a₆ p θ
  map_zero' := lambda_zero a₂ a₄ a₆ p θ
  map_add' := lambda_map_add a₂ a₄ a₆ p h

end ECCompute
