/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Defs
import ECCompute.Descent.DenominatorSquare
import ECCompute.Descent.Collinearity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The descent character: additivity (T1)

This file assembles the additivity of the descent character `λ_{p,θ}` defined in
`ECCompute.Descent.Defs`, using the denominator-is-a-square lemma (T1a,
`ECCompute.Descent.DenominatorSquare`) and the collinearity identity (T1b,
`ECCompute.Descent.Collinearity`).

## Main declarations

* `ECCompute.psi_mul` — `ψ_p` is multiplicative-to-additive on nonzero elements.
* `ECCompute.lambda_some_of_den_ne` — reduction of `λ` on an affine point to `ψ_p(X − θ)`.
* `ECCompute.lambda_map_add` — **the trusted theorem**: `λ` is additive.
* `ECCompute.lambdaHom`  — `λ` packaged as an `AddMonoidHom`.
* `ECCompute.lambdaHom_two_nsmul` — `λ` vanishes on `2·E(ℚ)` (follows for free from `ZMod 2`).
-/

open WeierstrassCurve

namespace ECCompute

open scoped Classical

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### The Legendre character `ψ_p` is a homomorphism away from zero

`ψ_p` sends squares to `0` and non-squares to `1` in `ZMod 2`.  On the nonzero elements of the
field `ZMod p` (`p` an odd prime) it is the quadratic-residue character transported along the
group isomorphism `{±1} ≅ ZMod 2`, hence multiplicative-to-additive: `ψ_p(ab) = ψ_p a + ψ_p b`.
We prove this via `quadraticChar`. -/

section Psi

variable {p}

/-- `ψ_p` vanishes on squares. -/
theorem psi_of_isSquare {a : ZMod p} (ha : IsSquare a) : psi p a = 0 :=
  if_pos ha

/-- Multiplying by a nonzero square does not change `ψ_p`. -/
theorem psi_mul_sq [Fact p.Prime] {a w : ZMod p} (hw : w ≠ 0) :
    psi p (w ^ 2 * a) = psi p a := by
  have hiff : IsSquare (w ^ 2 * a) ↔ IsSquare a := by
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s / w, by
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hw hw)]; linear_combination hs⟩
    · rintro ⟨r, rfl⟩
      exact ⟨w * r, by ring⟩
  unfold psi
  rw [hiff]

/-- On the nonzero elements of `ZMod p` (`p` an odd prime), `ψ_p` turns products into sums:
`ψ_p(ab) = ψ_p a + ψ_p b`.  Proved by transporting the multiplicativity of `quadraticChar`. -/
theorem psi_mul (hp : p.Prime) (_hodd : p ≠ 2) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    psi p (a * b) = psi p a + psi p b := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `IsSquare (a*b) ↔ (IsSquare a ↔ IsSquare b)` on nonzero elements, via `quadraticChar`.
  have key : IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    rw [← quadraticChar_one_iff_isSquare hab, ← quadraticChar_one_iff_isSquare ha,
      ← quadraticChar_one_iff_isSquare hb, map_mul]
    rcases quadraticChar_dichotomy ha with hA | hA <;>
      rcases quadraticChar_dichotomy hb with hB | hB <;>
      rw [hA, hB] <;> decide
  unfold psi
  by_cases hA : IsSquare a <;> by_cases hB : IsSquare b
  · rw [if_pos hA, if_pos hB, if_pos (key.mpr (by tauto)), add_zero]
  · rw [if_pos hA, if_neg hB, if_neg (fun h => hB ((key.mp h).mp hA)), zero_add]
  · rw [if_neg hA, if_pos hB, if_neg (fun h => hA ((key.mp h).mpr hB)), add_zero]
  · rw [if_neg hA, if_neg hB, if_pos (key.mpr (by tauto))]; decide

end Psi

/-! ### Reducing `λ` on an affine point to `ψ_p` of the reduced coordinate

For `P = (x, y)` on `E` with `p ∤ x.den`, write `X := (x : ZMod p)` (the rational cast) and
`w` with `x.den = w²` (T1a).  Then `α = x.num − θ·x.den = w²·(X − θ)`, so `ψ_p(α) = ψ_p(X − θ)`,
and the tangent branch `α = 0` is exactly `X = θ`. -/

/-- The reduced `x`-coordinate `(x : ZMod p)` of an affine point, as a plain field element. -/
noncomputable def xbar (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p := (x : ZMod p)

variable {a₂ a₄ a₆ p}

/-- Cast identity: `(x.num : ZMod p) = xbar · (x.den : ZMod p)` when `p ∤ x.den`. -/
theorem num_eq_xbar_mul_den [Fact p.Prime] {x : ℚ} (hd : (x.den : ZMod p) ≠ 0) :
    (x.num : ZMod p) = xbar p x * (x.den : ZMod p) := by
  rw [xbar, Rat.cast_def, div_mul_cancel₀ _ hd]

/-- `α = w² (X − θ)` where `x.den = w²`, hence `α` and `X − θ` differ by a nonzero square. -/
theorem alpha_eq [Fact p.Prime] {x : ℚ} {θ : ZMod p} {w : ℕ} (hden : x.den = w ^ 2)
    (hd : (x.den : ZMod p) ≠ 0) :
    (x.num : ZMod p) - θ * (x.den : ZMod p) = (w : ZMod p) ^ 2 * (xbar p x - θ) := by
  have hw : ((w : ZMod p)) ^ 2 = (x.den : ZMod p) := by rw [hden]; push_cast; ring
  rw [num_eq_xbar_mul_den hd, ← hw]; ring

/-- **Reduction of `λ`.**  For a point `some x y h` with `p ∤ x.den`, writing `X = (x : ZMod p)`,
the descent character is `ψ_p(f'(θ))` in the tangent case `X = θ` and `ψ_p(X − θ)` otherwise. -/
theorem lambda_some_of_den_ne [Fact p.Prime] {θ : ZMod p} {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    lambda a₂ a₄ a₆ p θ (.some x y h)
      = if xbar p x = θ then psi p (fderiv a₂ a₄ a₆ p θ) else psi p (xbar p x - θ) := by
  obtain ⟨w, hxden, _⟩ := den_isSquare_of_nonsingular a₂ a₄ a₆ h
  have hw : (w : ZMod p) ≠ 0 := by
    intro h0; apply hd; rw [hxden]; push_cast; rw [h0]; ring
  have halpha := alpha_eq (θ := θ) hxden hd
  change (if (x.den : ZMod p) = 0 then (0 : ZMod 2)
        else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psi p (fderiv a₂ a₄ a₆ p θ)
             else psi p ((x.num : ZMod p) - θ * (x.den : ZMod p))) = _
  rw [if_neg hd, halpha]
  by_cases hxt : xbar p x = θ
  · rw [if_pos (show (w : ZMod p) ^ 2 * (xbar p x - θ) = 0 by rw [hxt]; ring), if_pos hxt]
  · have hne : (w : ZMod p) ^ 2 * (xbar p x - θ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hw) (sub_ne_zero.mpr hxt)
    rw [if_neg hne, if_neg hxt, psi_mul_sq hw]

/-- `λ` on an affine point depends only on its `x`-coordinate: two points with equal `x`
have equal `λ`.  In particular `λ(-P) = λ(P)`, since negation fixes `x`. -/
theorem lambda_x_indep {θ : ZMod p} {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁}
    {h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) :
    lambda a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = lambda a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl

/-- **Collinear triple, character version.**  If `X₁, X₂, X₃` are the reduced `x`-coordinates
of three collinear points on `E` (encoded by the Vieta relations of the line `y = ℓx + m`),
all distinct from the root `θ`, then the `ψ_p`-values sum to zero.  This is the `𝔽ₚ`-arithmetic
heart of additivity: T1b makes `(X₁−θ)(X₂−θ)(X₃−θ)` a square, and `ψ_p` is additive on the
nonzero factors. -/
theorem psi_collinear (hp : p.Prime) (hp2 : p ≠ 2) {θ ℓ m X₁ X₂ X₃ : ZMod p}
    (hσ₁ : X₁ + X₂ + X₃ = ℓ ^ 2 - (a₂ : ZMod p))
    (hσ₂ : X₁ * X₂ + X₁ * X₃ + X₂ * X₃ = (a₄ : ZMod p) - 2 * ℓ * m)
    (hσ₃ : X₁ * X₂ * X₃ = m ^ 2 - (a₆ : ZMod p))
    (hroot : fval a₂ a₄ a₆ p θ = 0)
    (hX₁ : X₁ ≠ θ) (hX₂ : X₂ ≠ θ) (hX₃ : X₃ ≠ θ) :
    psi p (X₁ - θ) + psi p (X₂ - θ) + psi p (X₃ - θ) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hprod := prod_sub_theta_eq_lineSq_zmod a₂ a₄ a₆ p ℓ m X₁ X₂ X₃ θ hσ₁ hσ₂ hσ₃ hroot
  have h1 : X₁ - θ ≠ 0 := sub_ne_zero.mpr hX₁
  have h2 : X₂ - θ ≠ 0 := sub_ne_zero.mpr hX₂
  have h3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr hX₃
  have hpm : psi p ((X₁ - θ) * (X₂ - θ) * (X₃ - θ)) = 0 := by
    rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
  rwa [psi_mul hp hp2 (mul_ne_zero h1 h2) h3, psi_mul hp hp2 h1 h2] at hpm

end ECCompute

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### The trusted theorem: additivity -/

/-- **Descent character is additive.**  Under the hypotheses `p ∤ 6Δ` and `f(θ) ≡ 0`, the
descent character `λ_{p,θ}` is a homomorphism `(E(ℚ), +) → (ZMod 2, +)`.  This is the one
trusted mathematical input of the whole development; see the proof plan below. -/
theorem lambda_map_add {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ (P + Q) = lambda a₂ a₄ a₆ p θ P + lambda a₂ a₄ a₆ p θ Q := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Affine.Point.zero_def, zero_add, lambda_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Affine.Point.zero_def, add_zero, lambda_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve a₂ a₄ a₆).toAffine.negY x₂ y₂
  · -- `Q = -P`: the sum is `O`, and both summands share the `x`-coordinate, so `λP + λQ = 2λP = 0`.
    rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, lambda_zero,
      lambda_x_indep (h₁ := h₁) (h₂ := h₂) hxy.1, ← two_mul,
      show (2 : ZMod 2) = 0 from by decide, zero_mul]
  · -- Generic case: the secant/tangent gives `P + Q = some x₃ y₃`, and `P`, `Q`, `-(P + Q)`
    -- are three collinear points on `E` with `x`-coordinates `x₁, x₂, x₃ = addX x₁ x₂ ℓ`.
    -- Since `λ` ignores the `y`-coordinate, `λ(P + Q) = λ(-(P + Q)) = ψ_p(xbar x₃ − θ)`.
    -- The arithmetic heart `psi_collinear` closes the "good, non-tangent" subcase: taking
    -- `Xᵢ = xbar xᵢ`, `ℓ, m` the reduced slope/intercept, T1b makes the product a square, and
    -- the three `λ`-values (via `lambda_some_of_den_ne`) sum to zero, giving additivity in the
    -- character group `ZMod 2`.
    --
    -- REMAINING BRIDGE (the T1d core, blocked — see report): to feed `psi_collinear` one must
    -- produce, from the `ℚ` group-law data, the reduced Vieta relations `hσ₁, hσ₂, hσ₃` in
    -- `ZMod p` and the genericity `xbar xᵢ ≠ θ`, plus dispatch the exceptional patches
    -- `(xᵢ.den : ZMod p) = 0` (a point reducing to `O` mod `p`) and `xbar xᵢ = θ` (tangent /
    -- 2-torsion mod `p`).  Because `Rat.cast : ℚ → ZMod p` is *not* a ring homomorphism in
    -- positive characteristic, casting the curve/line/`addX` identities requires clearing
    -- denominators per point (T1a gives `x.den = w²`) and controlling `p`-divisibility of the
    -- slope denominator `x₁ − x₂` — i.e. the reduction map `E(ℚ) → E(𝔽ₚ)`, which mathlib lacks.
    sorry

/-- The descent character `λ_{p,θ}` as an `AddMonoidHom E(ℚ) → ZMod 2`. -/
noncomputable def lambdaHom {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 where
  toFun := lambda a₂ a₄ a₆ p θ
  map_zero' := lambda_zero a₂ a₄ a₆ p θ
  map_add' := lambda_map_add a₂ a₄ a₆ p h

@[simp]
theorem lambdaHom_apply {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambdaHom a₂ a₄ a₆ p h P = lambda a₂ a₄ a₆ p θ P :=
  rfl

/-- **The descent character vanishes on `2·E(ℚ)`.**  Immediate from being a homomorphism
into `ZMod 2`, where `x + x = 0` for every `x`.  Hence `λ_{p,θ}` factors through
`E(ℚ)/2E(ℚ)`. -/
theorem lambdaHom_two_nsmul {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambdaHom a₂ a₄ a₆ p h (2 • P) = 0 := by
  rw [two_nsmul, map_add, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

/-- Restated: `λ_{p,θ}` kills every element of the image of doubling. -/
theorem lambdaHom_apply_eq_zero_of_mem_range_two_nsmul {θ : ZMod p}
    (h : DescentHyp a₂ a₄ a₆ p θ) {R : (curve a₂ a₄ a₆).toAffine.Point}
    (hR : ∃ P, R = 2 • P) : lambdaHom a₂ a₄ a₆ p h R = 0 := by
  obtain ⟨P, rfl⟩ := hR
  exact lambdaHom_two_nsmul a₂ a₄ a₆ p h P

end ECCompute
