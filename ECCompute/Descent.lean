/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Defs
import ECCompute.Descent.DenominatorSquare
import ECCompute.Descent.Collinearity
import ECCompute.Descent.ReducedArith
import ECCompute.Descent.PsiBase
import ECCompute.Descent.Reduction.Def
import ECCompute.Descent.Reduction.Hom
import ECCompute.Descent.Reduction.EpsFinite
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.ZMod
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

/-! ### Reducing `λ` on an affine point to `ψ_p` of the reduced coordinate

For `P = (x, y)` on `E` with `p ∤ x.den`, write `X := (x : ZMod p)` (the rational cast) and
`w` with `x.den = w²` (T1a).  Then `α = x.num − θ·x.den = w²·(X − θ)`, so `ψ_p(α) = ψ_p(X − θ)`,
and the tangent branch `α = 0` is exactly `X = θ`. -/

variable {a₂ a₄ a₆ p}

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

/-- **Reduction of `λ` to `O`.**  When `p ∣ x.den` the point `some x y h` reduces to `O` of
`E/𝔽ₚ`, and `λ` vanishes on it by definition. -/
theorem lambda_some_of_den_zero {θ : ZMod p} {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    lambda a₂ a₄ a₆ p θ (.some x y h) = 0 := by
  change (if (x.den : ZMod p) = 0 then (0 : ZMod 2)
      else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psi p (fderiv a₂ a₄ a₆ p θ)
           else psi p ((x.num : ZMod p) - θ * (x.den : ZMod p))) = _
  rw [if_pos hd]

/-- `λ` on an affine point depends only on its `x`-coordinate: two points with equal `x`
have equal `λ`.  In particular `λ(-P) = λ(P)`, since negation fixes `x`. -/
theorem lambda_x_indep {θ : ZMod p} {x₁ y₁ x₂ y₂ : ℚ}
    {h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁}
    {h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) :
    lambda a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = lambda a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl

/-- **Additivity of `λ`, good-reduction case.**  When `P = (x₁, y₁)` and `Q = (x₂, y₂)` have
distinct `x`-coordinates over `ℚ`, all of `x₁, x₂` and the sum's `x`-coordinate reduce (good
denominators), and the reduced `x`-coordinates `X₁, X₂` are distinct mod `p`, then
`λ(P + Q) = λ P + λ Q`.  This covers the generic (non-`2`-torsion) case together with the three
`2`-torsion patches `Xᵢ = θ`: the collinearity square `(X₁ − θ)(X₂ − θ)(X₃ − θ) = (ℓ̄θ + m̄)²`
(T1b via `reduced_on_curve`/`reduced_addX`) gives additivity of `ψ_p` on the nonzero factors,
while at a factor `Xᵢ = θ` the identity `f'(θ) = (Xⱼ − θ)(Xₖ − θ)` (`fderiv_eq_prod`) replaces
that factor by `f'(θ)`, which is nonzero by `fderiv_ne_zero`. -/
theorem lambda_map_add_of_good [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curve a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hne : x₁ ≠ x₂)
    (hdx1 : (x₁.den : ZMod p) ≠ 0) (hdx2 : (x₂.den : ZMod p) ≠ 0)
    (hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0)
    (hbne : (x₁ : ZMod p) ≠ (x₂ : ZMod p)) :
    lambda a₂ a₄ a₆ p θ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = lambda a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) + lambda a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  have hp2 : p ≠ 2 := fun hp => h.ne_six (hp ▸ ⟨3, rfl⟩)
  have hdy1 : (y₁.den : ZMod p) ≠ 0 := ydenom_ne_zero h₁.1 hdx1
  have hdy2 : (y₂.den : ZMod p) ≠ 0 := ydenom_ne_zero h₂.1 hdx2
  set X₁ : ZMod p := (x₁ : ZMod p) with hX1
  set X₂ : ZMod p := (x₂ : ZMod p) with hX2
  set Y₁ : ZMod p := (y₁ : ZMod p) with hY1
  set Y₂ : ZMod p := (y₂ : ZMod p) with hY2
  set X₃ : ZMod p := (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ℚ) : ZMod p) with hX3
  have hdiff : X₁ - X₂ ≠ 0 := sub_ne_zero.mpr hbne
  set ℓb : ZMod p := (Y₁ - Y₂) / (X₁ - X₂) with hℓb
  set mb : ZMod p := Y₁ - ℓb * X₁ with hmb
  have hℓmul : ℓb * (X₁ - X₂) = Y₁ - Y₂ := div_mul_cancel₀ _ hdiff
  have hm1 : ℓb * X₁ + mb = Y₁ := by rw [hmb]; ring
  have hm2 : ℓb * X₂ + mb = Y₂ := by rw [hmb]; linear_combination -hℓmul
  have hpt1 : (ℓb * X₁ + mb) ^ 2 = X₁ ^ 3 + (a₂ : ZMod p) * X₁ ^ 2 + (a₄ : ZMod p) * X₁ + a₆ := by
    rw [hm1]; exact reduced_on_curve h₁.1 hdx1 hdy1
  have hpt2 : (ℓb * X₂ + mb) ^ 2 = X₂ ^ 3 + (a₂ : ZMod p) * X₂ ^ 2 + (a₄ : ZMod p) * X₂ + a₆ := by
    rw [hm2]; exact reduced_on_curve h₂.1 hdx2 hdy2
  have hRELZ := reduced_addX hne hdx1 hdx2 hdy1 hdy2 hdx3
  have hx3 : X₃ = ℓb ^ 2 - (a₂ : ZMod p) - X₁ - X₂ := by
    have hcancel : (X₃ + (a₂ : ZMod p) + X₁ + X₂) * (X₁ - X₂) ^ 2 = ℓb ^ 2 * (X₁ - X₂) ^ 2 := by
      rw [hRELZ]; linear_combination (-(Y₁ - Y₂) - ℓb * (X₁ - X₂)) * hℓmul
    have := mul_right_cancel₀ (pow_ne_zero 2 hdiff) hcancel
    linear_combination this
  have hθroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    have := h.root; simpa [fval] using this
  -- Vieta relations of the collinear triple, and the collinearity square.
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb
    X₁ X₂ X₃ hbne hx3 hpt1 hpt2
  have hprod : (X₁ - θ) * (X₂ - θ) * (X₃ - θ) = (ℓb * θ + mb) ^ 2 :=
    prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X₁ X₂ X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot
  -- `f'(θ)` is nonzero, and equals the product of the two non-`θ` factors at each `2`-torsion case.
  have hfd_ne : fderiv a₂ a₄ a₆ p θ ≠ 0 := fderiv_ne_zero h
  have hfd1 : X₁ = θ → fderiv a₂ a₄ a₆ p θ = (X₂ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X₁ X₂ X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot hc
  have hfd2 : X₂ = θ → fderiv a₂ a₄ a₆ p θ = (X₁ - θ) * (X₃ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X₂ X₁ X₃ θ
      (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
      hθroot hc
  have hfd3 : X₃ = θ → fderiv a₂ a₄ a₆ p θ = (X₁ - θ) * (X₂ - θ) := fun hc =>
    fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X₃ X₁ X₂ θ
      (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
      hθroot hc
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne,
      lambda_some_of_den_ne (h := (curve a₂ a₄ a₆).toAffine.nonsingular_add h₁ h₂
        (fun hxy => hne hxy.left)) hdx3,
      lambda_some_of_den_ne h₁ hdx1, lambda_some_of_den_ne h₂ hdx2]
  simp only [xbar, ← hX1, ← hX2, ← hX3]
  -- Bookkeeping in `ZMod 2` (`x + x = 0`), split on which reduced `x`-coordinate hits `θ`.
  have hz : ∀ a b : ZMod 2, a + b + a = b := by decide
  have hz' : ∀ a b : ZMod 2, b = a + (a + b) := by decide
  have hzero : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by decide
  by_cases c1 : X₁ = θ
  · -- `P` is `2`-torsion mod `p`; then `X₂ ≠ θ` (as `X₁ ≠ X₂`) and `X₃ ≠ θ` (else `f'(θ) = 0`).
    have hX2ne : X₂ ≠ θ := fun hc => hbne (c1.trans hc.symm)
    have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd1 c1, hc]; ring)
    rw [if_neg hX3ne, if_pos c1, if_neg hX2ne, hfd1 c1,
      psi_mul h.prime hp2 (sub_ne_zero.mpr hX2ne) (sub_ne_zero.mpr hX3ne)]
    exact (hz _ _).symm
  by_cases c2 : X₂ = θ
  · -- `Q` is `2`-torsion mod `p`; symmetric to the previous case.
    have hX3ne : X₃ ≠ θ := fun hc => hfd_ne (by rw [hfd2 c2, hc]; ring)
    rw [if_neg hX3ne, if_neg c1, if_pos c2, hfd2 c2,
      psi_mul h.prime hp2 (sub_ne_zero.mpr c1) (sub_ne_zero.mpr hX3ne)]
    exact hz' _ _
  by_cases c3 : X₃ = θ
  · -- `P + Q` is `2`-torsion mod `p`.
    rw [if_pos c3, if_neg c1, if_neg c2, hfd3 c3,
      psi_mul h.prime hp2 (sub_ne_zero.mpr c1) (sub_ne_zero.mpr c2)]
  · -- Generic case: `ψ_p` is additive on the three nonzero factors of the collinearity square.
    have hs1 : X₁ - θ ≠ 0 := sub_ne_zero.mpr c1
    have hs2 : X₂ - θ ≠ 0 := sub_ne_zero.mpr c2
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((X₁ - θ) * (X₂ - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓb * θ + mb, by ring⟩
    rw [psi_mul h.prime hp2 (mul_ne_zero hs1 hs2) hs3, psi_mul h.prime hp2 hs1 hs2] at hpm
    rw [if_neg c3, if_neg c1, if_neg c2]
    exact hzero _ _ _ hpm

/-- **Additivity of `λ`, good doubling case.**  If `P = (x, y)` reduces to a non-`2`-torsion
point (`Y ≠ 0`) with good denominators — including the doubled `x`-coordinate — then the descent
character vanishes on `2P`.  This is the doubling analogue of `lambda_map_add_of_good`: the
collinear triple is `X, X, X₃` with `X₃ = ℓ̄² − a₂ − 2X` for the reduced tangent slope
`ℓ̄ = f'(X)/(2Y)` (`reduced_doubleX`), so the double-root Vieta relations make
`(X − θ)²(X₃ − θ)` a square and `ψ_p(X₃ − θ) = 0`. -/
theorem lambda_double_of_good [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    {x y : ℚ} (hP : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hy0 : (y : ZMod p) ≠ 0) (hdx : (x.den : ZMod p) ≠ 0)
    (hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x x
        ((curve a₂ a₄ a₆).toAffine.slope x x y y)).den : ZMod p) ≠ 0) :
    lambda a₂ a₄ a₆ p θ (.some x y hP + .some x y hP) = 0 := by
  have hp2 : p ≠ 2 := fun hp => h.ne_six (hp ▸ ⟨3, rfl⟩)
  have hyℚ : y ≠ 0 := fun hh => hy0 (by rw [hh, Rat.cast_zero])
  have hdy : (y.den : ZMod p) ≠ 0 := ydenom_ne_zero hP.1 hdx
  have hyne : y ≠ (curve a₂ a₄ a₆).toAffine.negY x y := by
    rw [show (curve a₂ a₄ a₆).toAffine.negY x y = -y by
      simp [WeierstrassCurve.Affine.negY, curve]]
    intro hh; apply hyℚ; linarith
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hd)
  have hdbl := reduced_doubleX hyℚ hdx hdy hdx3
  have hcurve := reduced_on_curve hP.1 hdx hdy
  have hθroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    have := h.root; simpa [fval] using this
  set X : ZMod p := (x : ZMod p) with hX
  set Y : ZMod p := (y : ZMod p) with hY
  set X₃ : ZMod p := ((curve a₂ a₄ a₆).toAffine.addX x x
    ((curve a₂ a₄ a₆).toAffine.slope x x y y) : ZMod p) with hX3
  have h2Y : (2 : ZMod p) * Y ≠ 0 := mul_ne_zero h2 hy0
  set ℓb : ZMod p := (3 * X ^ 2 + 2 * (a₂ : ZMod p) * X + (a₄ : ZMod p)) / (2 * Y) with hℓbdef
  have hℓ2Y : ℓb * (2 * Y) = 3 * X ^ 2 + 2 * (a₂ : ZMod p) * X + (a₄ : ZMod p) :=
    div_mul_cancel₀ _ h2Y
  have hx3 : X₃ = ℓb ^ 2 - (a₂ : ZMod p) - 2 * X := by
    have hcancel : (X₃ + (a₂ : ZMod p) + 2 * X) * (2 * Y) ^ 2 = ℓb ^ 2 * (2 * Y) ^ 2 := by
      rw [hdbl]
      linear_combination
        (-(3 * X ^ 2 + 2 * (a₂ : ZMod p) * X + (a₄ : ZMod p)) - ℓb * (2 * Y)) * hℓ2Y
    have := mul_right_cancel₀ (pow_ne_zero 2 h2Y) hcancel
    linear_combination this
  set mb : ZMod p := Y - ℓb * X with hmb
  have hm : ℓb * X + mb = Y := by rw [hmb]; ring
  have hpt : (ℓb * X + mb) ^ 2
      = X ^ 3 + (a₂ : ZMod p) * X ^ 2 + (a₄ : ZMod p) * X + (a₆ : ZMod p) := by
    rw [hm]; exact hcurve
  have htan : 3 * X ^ 2 + 2 * (a₂ : ZMod p) * X + (a₄ : ZMod p) = 2 * ℓb * (ℓb * X + mb) := by
    rw [hm]; linear_combination -hℓ2Y
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_double_root (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p)
    ℓb mb X X₃ hpt htan hx3
  have hprod : (X - θ) * (X - θ) * (X₃ - θ) = (ℓb * θ + mb) ^ 2 :=
    prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X X X₃ θ
      hσ₁ hσ₂ hσ₃ hθroot
  have hXθ : X ≠ θ := by
    intro hc
    apply hy0
    have hYsq : Y ^ 2 = 0 := by rw [hcurve, hc]; exact hθroot
    exact pow_eq_zero_iff (by norm_num) |>.mp hYsq
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne, lambda_some_of_den_ne _ hdx3]
  simp only [xbar, ← hX3]
  by_cases c3 : X₃ = θ
  · rw [if_pos c3]
    have hfd : fderiv a₂ a₄ a₆ p θ = (X - θ) * (X - θ) := by
      have := fderiv_eq_prod (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓb mb X₃ X X θ
        (by linear_combination hσ₁) (by linear_combination hσ₂) (by linear_combination hσ₃)
        hθroot c3
      simpa [fderiv] using this
    rw [hfd]; exact psi_of_isSquare ⟨X - θ, by ring⟩
  · rw [if_neg c3]
    have hs : X - θ ≠ 0 := sub_ne_zero.mpr hXθ
    have hs3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr c3
    have hpm : psi p ((X - θ) * (X - θ) * (X₃ - θ)) = 0 := by
      rw [hprod]; exact psi_of_isSquare ⟨ℓb * θ + mb, by ring⟩
    rw [psi_mul h.prime hp2 (mul_ne_zero hs hs) hs3, psi_mul h.prime hp2 hs hs] at hpm
    have hfin : ∀ a b : ZMod 2, a + a + b = 0 → b = 0 := by decide
    exact hfin _ _ hpm

end ECCompute

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### The trusted theorem: additivity via the reduction factorisation

Additivity of `λ_{p,θ}` is obtained by factoring it as the composition
`λ = εp_finite ∘ red_p`, where `red_p : E(ℚ) → E(𝔽ₚ)` is the reduction map
(`ECCompute.Descent.Reduction.Hom`, an `AddMonoidHom`) and `εp_finite : E(𝔽ₚ) → ZMod 2` is the
finite-field descent character (`ECCompute.Descent.Reduction.EpsFinite`, also an
`AddMonoidHom`).  Additivity of `λ` is then just `map_add` of a composition of homomorphisms.
The reduction map lands in `((curveℤ …).map (ℤ → ZMod p)).toAffine.Point`, which is the same
curve as `reducedCurve … p` up to the definitional equality `map_eq_reducedCurve`; we transport
across it with `Point.congr`. -/

section Congr

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}

/-- Transport affine points along an equality of Weierstrass curves, as an additive
homomorphism `W₁.toAffine.Point →+ W₂.toAffine.Point`. -/
def Point.congr (hce : W₁ = W₂) : W₁.toAffine.Point →+ W₂.toAffine.Point where
  toFun P := hce ▸ P
  map_zero' := by cases hce; rfl
  map_add' _ _ := by cases hce; rfl

@[simp]
theorem Point.congr_some (hce : W₁ = W₂) {X Y : F} (hns : W₁.toAffine.Nonsingular X Y) :
    Point.congr hce (Affine.Point.some X Y hns) = Affine.Point.some X Y (hce ▸ hns) := by
  cases hce; rfl

end Congr

/-- The reduction of the integral model mod `p` is the reduced curve `reducedCurve … p`. -/
theorem map_eq_reducedCurve :
    (curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p)) = reducedCurve a₂ a₄ a₆ p := by
  rw [map_curveℤ_zmod]; rfl

/-- The descent character `λ_{p,θ}` presented as the composition
`εp_finite θ ∘ (transport) ∘ red_p`, packaged as an `AddMonoidHom E(ℚ) → ZMod 2`.  This is the
factorisation that makes additivity of `λ` free (see `lambda_map_add`). -/
noncomputable def redCharHom [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →+ ZMod 2 :=
  (εpHom h).comp ((Point.congr (map_eq_reducedCurve a₂ a₄ a₆ p)).comp (redHom a₂ a₄ a₆ p hΔ))

/-- **The bridge.**  On each point, `λ_{p,θ}` agrees with the reduction composition
`εp_finite θ ∘ red_p`.  The three cases mirror the definition of `red_p`: the origin (both `0`),
`p ∤ x.den` (reduced affine coordinates, via `lambda_some_of_den_ne` and `red_p_of_den_ne`), and
`p ∣ x.den` (reduces to the origin, via `lambda_some_of_den_zero` and `red_p_of_den_zero`). -/
theorem lambda_eq_εp_red [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ P = redCharHom a₂ a₄ a₆ p h hΔ P := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, lambda_zero, map_zero]
  | some x y hns =>
    rw [redCharHom, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, redHom_apply]
    by_cases hd : (x.den : ZMod p) = 0
    · rw [lambda_some_of_den_zero hns hd, red_p_of_den_zero a₂ a₄ a₆ p hΔ hns hd,
        map_zero, εpHom_apply, εp_finite_zero]
    · rw [lambda_some_of_den_ne hns hd, red_p_of_den_ne a₂ a₄ a₆ p hΔ hns hd,
        Point.congr_some, εpHom_apply, εp_finite_some]
      simp only [xbar]

/-- The bridge, spelled out with the reduction map: `λ_{p,θ} P = εp_finite θ (red_p P)` (up to the
transport `Point.congr` across `map_eq_reducedCurve`). -/
theorem lambda_eq_εp_finite_red [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (P : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ P
      = εp_finite a₂ a₄ a₆ p θ
          (Point.congr (map_eq_reducedCurve a₂ a₄ a₆ p) (red_p a₂ a₄ a₆ p hΔ P)) := by
  rw [lambda_eq_εp_red a₂ a₄ a₆ p h hΔ, redCharHom, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, εpHom_apply, redHom_apply]

/-- **Descent character is additive.**  Under the hypotheses `p ∤ 6Δ` and `f(θ) ≡ 0`, the
descent character `λ_{p,θ}` is a homomorphism `(E(ℚ), +) → (ZMod 2, +)`.  This is now immediate
from the factorisation `λ = εp_finite ∘ red_p` (`lambda_eq_εp_red`): both factors are
homomorphisms, so additivity is `map_add` of their composition `redCharHom`. -/
theorem lambda_map_add {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ (P + Q) = lambda a₂ a₄ a₆ p θ P + lambda a₂ a₄ a₆ p θ Q := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0 := by
    have hval : (curve a₂ a₄ a₆).Δ = ((curveℤ a₂ a₄ a₆).Δ : ℚ) := by
      rw [← baseChange_curveℤ_ℚ, WeierstrassCurve.baseChange, algebraMap_int_eq,
        WeierstrassCurve.map_Δ, eq_intCast]
    have hnum : ((curve a₂ a₄ a₆).Δ.num : ZMod p) = ((curveℤ a₂ a₄ a₆).Δ : ZMod p) := by
      rw [hval, Rat.num_intCast]
    rw [← hnum]; exact h.discr
  simp only [lambda_eq_εp_red a₂ a₄ a₆ p h hΔ, map_add]

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
