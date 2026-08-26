/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character
public import ECCompute.Theory.Descent.CharacterFacts
import ECCompute.Theory.Descent.PointArith
import ECCompute.Theory.Descent.Reduction.Map
import ECCompute.Theory.Descent.Reduction.RedHom
import ECCompute.Theory.Descent.Reduction.FiniteCharacter

/-!
# The descent character: additivity

This file assembles the additivity of the descent character `λ_{p,θ}` defined in
`ECCompute.Descent.Character`. Additivity is obtained by factoring `λ` through the reduction map
`redP : E(ℚ) → E(𝔽ₚ)` and the finite-field descent character `εpFinite`, both of which are
additive homomorphisms (see `ECCompute.Descent.Reduction.RedHom` and
`ECCompute.Descent.Reduction.FiniteCharacter`).

## Main declarations

* `ECCompute.lambdaHom`: `λ` packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}

/-! ### Reducing `λ` on an affine point to `ψ_p` of the reduced coordinate -/

/-- Reduction of `λ` on an affine point with `p ∤ x.den` to `ψ_p` of the reduced coordinate:
`ψ_p(f'(θ))` when `xbar p x = θ`, and `ψ_p(xbar p x - θ)` otherwise. -/
theorem lambda_some_of_den_ne [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    lambda θ (.some x y h)
      = if xbar p x = θ then psi p (fderiv (R := ZMod p) a₂ a₄ θ) else psi p (xbar p x - θ) := by
  obtain ⟨w, hxden, _⟩ := den_isSquare h.1
  have hw : (w : ZMod p) ≠ 0 := by intro h0; apply hd; rw [hxden]; grind
  have halpha : x.num - θ * x.den = (w : ZMod p) ^ 2 * (xbar p x - θ) := by
    rw [num_eq_xbar_mul_den hd, hxden]; grind
  have hp : p.Prime := Fact.out
  simp only [lambda]
  grind [psi_mul_sq hp]

/-- When `p ∣ x.den` the point reduces to `O` of `E/𝔽ₚ`, where `λ` vanishes. -/
theorem lambda_some_of_den_zero {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    lambda θ (.some x y h) = 0 := by simp only [lambda, if_pos hd]

/-! ### Additivity via the reduction factorization

Additivity of `λ_{p,θ}` factors it as `λ = εpFinite ∘ redP`, with `redP : E(ℚ) → E(𝔽ₚ)`
(`ECCompute.Descent.Reduction.RedHom`) and `εpFinite : E(𝔽ₚ) → ZMod 2`
(`ECCompute.Descent.Reduction.FiniteCharacter`) both `AddMonoidHom`s. See `lambda_map_add`. -/

/-- The descent character `λ_{p,θ}` presented as the composition `εpFinite θ ∘ redP`, packaged
as an `AddMonoidHom E(ℚ) → ZMod 2`. See `lambda_map_add`. -/
noncomputable def redCharHom [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 :=
  (εpHom h).comp (redHom hΔ)

/-- On each point, `λ_{p,θ}` agrees with the reduction composition `εpFinite θ ∘ redP`. -/
theorem lambda_eq_εp_red [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda θ P = redCharHom h hΔ P := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, lambda_zero, map_zero]
  | some x y hns =>
    rw [redCharHom, AddMonoidHom.comp_apply, redHom_apply]
    by_cases hd : (x.den : ZMod p) = 0
    · grind [lambda_some_of_den_zero, redP_of_den_zero]
    · grind [lambda_some_of_den_ne, redP_of_den_ne, εpHom_apply, εpFinite_some, xbar]

/-- The descent character `λ_{p,θ}` is additive, i.e. a homomorphism `(E(ℚ), +) → (ZMod 2, +)`. -/
theorem lambda_map_add (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda θ (P + Q) = lambda θ P + lambda θ Q := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0 := by
    have hval : (curve a₂ a₄ a₆).Δ = (curveℤ a₂ a₄ a₆).Δ := by
      rw [← map_curveℤ_ℚ, map_Δ, eq_intCast]
    rw [← Rat.num_intCast (curveℤ a₂ a₄ a₆).Δ]
    grind
  simp only [lambda_eq_εp_red h hΔ, map_add]

/-- The descent character `λ_{p,θ}` as an `AddMonoidHom E(ℚ) → ZMod 2`. -/
@[expose, simps]
public noncomputable def lambdaHom (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 where
  toFun := lambda θ
  map_zero' := lambda_zero
  map_add' := by exact lambda_map_add h

end ECCompute
