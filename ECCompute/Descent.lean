/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Defs
import ECCompute.Descent.DenominatorSquare
import ECCompute.Descent.Collinearity
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
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

/-! ### Elementary reduction mod `p` (T1d)

The reduction map `E(ℚ) → E(𝔽ₚ)` is not available in mathlib, and `Rat.cast : ℚ → ZMod p` is
*not* a ring homomorphism in characteristic `p`.  We nevertheless transfer the group-law data of
a collinear triple to `ZMod p` in the *good-reduction* case by clearing denominators:
`Int.cast : ℤ → ZMod p` **is** a ring hom, and the conditional casts
`Rat.cast_add_of_ne_zero`, `Rat.cast_sub_of_ne_zero`, `Rat.cast_mul_of_ne_zero` push `Rat.cast`
through sums/products whose denominators survive reduction (`(·.den : ZMod p) ≠ 0`).  The
divisibility lemmas `Rat.add_den_dvd`, `Rat.sub_den_dvd`, `Rat.mul_den_dvd` give closure of this
"good denominator" predicate. -/

/-- If `a ∣ b` and `b`'s reduction is nonzero, so is `a`'s. -/
theorem den_ne_zero_of_dvd {a b : ℕ} (h : a ∣ b) (hb : (b : ZMod p) ≠ 0) :
    (a : ZMod p) ≠ 0 := fun ha =>
  hb ((ZMod.natCast_eq_zero_iff b p).mpr (((ZMod.natCast_eq_zero_iff a p).mp ha).trans h))

/-- Good denominators are closed under addition. -/
theorem den_add_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x + y).den : ZMod p) ≠ 0 :=
  den_ne_zero_of_dvd (Rat.add_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- Good denominators are closed under subtraction. -/
theorem den_sub_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x - y).den : ZMod p) ≠ 0 :=
  den_ne_zero_of_dvd (Rat.sub_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- Good denominators are closed under multiplication. -/
theorem den_mul_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x * y).den : ZMod p) ≠ 0 :=
  den_ne_zero_of_dvd (Rat.mul_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- **Reduced on-curve equation.**  A ℚ-point `(x, y)` on `E` with good denominators reduces to a
point of `E` over `ZMod p`.  Proved by clearing denominators to an integer identity (cast via the
genuine ring hom `Int.cast`) and rewriting `Rat.cast` as `num / den`. -/
theorem reduced_on_curve [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y)
    (hdx : (x.den : ZMod p) ≠ 0) (hdy : (y.den : ZMod p) ≠ 0) :
    (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + (a₂ : ZMod p) * (x : ZMod p) ^ 2
      + (a₄ : ZMod p) * (x : ZMod p) + (a₆ : ZMod p) := by
  have heq : y ^ 2 = x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) := by
    have := (WeierstrassCurve.Affine.equation_iff (W := (curve a₂ a₄ a₆).toAffine) x y).mp h
    simpa [curve] using this
  have hx : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * (y.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast y.den_ne_zero)).mp (Rat.num_div_den y)
  have key : (y.num ^ 2 * (x.den : ℤ) ^ 3 : ℤ)
      = (x.num ^ 3 + a₂ * x.num ^ 2 * x.den + a₄ * x.num * (x.den : ℤ) ^ 2
          + a₆ * (x.den : ℤ) ^ 3) * (y.den : ℤ) ^ 2 := by
    have hQ : (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 3
        = ((x.num : ℚ) ^ 3 + a₂ * (x.num : ℚ) ^ 2 * x.den + a₄ * (x.num : ℚ) * (x.den : ℚ) ^ 2
            + a₆ * (x.den : ℚ) ^ 3) * (y.den : ℚ) ^ 2 := by
      rw [hx, hy]; linear_combination ((x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2) * heq
    exact_mod_cast hQ
  have keyZ : (y.num : ZMod p) ^ 2 * (x.den : ZMod p) ^ 3
      = ((x.num : ZMod p) ^ 3 + (a₂ : ZMod p) * (x.num : ZMod p) ^ 2 * (x.den : ZMod p)
          + (a₄ : ZMod p) * (x.num : ZMod p) * (x.den : ZMod p) ^ 2
          + (a₆ : ZMod p) * (x.den : ZMod p) ^ 3) * (y.den : ZMod p) ^ 2 := by
    have := congrArg (Int.cast : ℤ → ZMod p) key
    push_cast at this
    linear_combination this
  simp only [Rat.cast_def]
  field_simp
  linear_combination keyZ

/-- **Reduced secant relation.**  For `x₁ ≠ x₂` and good denominators, the ℚ identity
`(x₃ + a₂ + x₁ + x₂)(x₁ − x₂)² = (y₁ − y₂)²` (where `x₃ = addX x₁ x₂ (slope …)` and
`slope · (x₁ − x₂) = y₁ − y₂`) reduces mod `p` by pushing `Rat.cast` through the conditional cast
lemmas. -/
theorem reduced_addX [Fact p.Prime] {x₁ x₂ y₁ y₂ : ℚ} (hne : x₁ ≠ x₂)
    (hdx1 : (x₁.den : ZMod p) ≠ 0) (hdx2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂) : ZMod p)
      + (a₂ : ZMod p) + (x₁ : ZMod p) + (x₂ : ZMod p)) * ((x₁ : ZMod p) - (x₂ : ZMod p)) ^ 2
      = ((y₁ : ZMod p) - (y₂ : ZMod p)) ^ 2 := by
  set ℓ := (curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curve a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, WeierstrassCurve.Affine.slope_of_X_ne hne]; field_simp
  have haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
    rw [hx3def]; simp only [WeierstrassCurve.Affine.addX, curve]; ring
  have REL : (x₃ + (a₂ : ℚ) + x₁ + x₂) * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 := by
    rw [haddX]; linear_combination (ℓ * (x₁ - x₂) + (y₁ - y₂)) * hℓ
  have hcast : (((x₃ + (a₂ : ℚ) + x₁ + x₂) * (x₁ - x₂) ^ 2 : ℚ) : ZMod p)
      = (((y₁ - y₂) ^ 2 : ℚ) : ZMod p) := by rw [REL]
  rw [Rat.cast_mul_of_ne_zero (den_add_ne_zero (den_add_ne_zero
        (den_add_ne_zero hdx3 (by simp)) hdx1) hdx2) (by
        rw [Rat.den_pow, Nat.cast_pow]; exact pow_ne_zero _ (den_sub_ne_zero hdx1 hdx2)),
      Rat.cast_pow, Rat.cast_pow,
      Rat.cast_sub_of_ne_zero hdx1 hdx2,
      Rat.cast_sub_of_ne_zero hdy1 hdy2] at hcast
  rw [Rat.cast_add_of_ne_zero (den_add_ne_zero (den_add_ne_zero hdx3 (by simp)) hdx1) hdx2,
      Rat.cast_add_of_ne_zero (den_add_ne_zero hdx3 (by simp)) hdx1,
      Rat.cast_add_of_ne_zero hdx3 (by simp)] at hcast
  rw [Rat.cast_intCast] at hcast
  exact hcast

/-- The `y`-denominator reduces well whenever the `x`-denominator does (via T1a,
`x.den = w²`, `y.den = w³`). -/
theorem ydenom_ne_zero [Fact p.Prime] {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Equation x y) (hdx : (x.den : ZMod p) ≠ 0) :
    (y.den : ZMod p) ≠ 0 := by
  obtain ⟨w, hxw, hyw⟩ := den_isSquare a₂ a₄ a₆ h
  have hw : (w : ZMod p) ≠ 0 := by
    intro h0; apply hdx; rw [hxw]; push_cast; rw [h0]; ring
  rw [hyw]; push_cast; exact pow_ne_zero 3 hw

/-- **The descent derivative `f'(θ)` is nonzero.**  Since `p ∤ 6Δ` and `θ` is a root of `f`,
`θ` is a *simple* root: `disc(f) = f'(θ)² · (B² − 4C)` for the complementary quadratic factor
`x² + Bx + C = f(x)/(x − θ)`, and `Δ = 16·disc(f)`, so `f'(θ) = 0` would force `Δ ≡ 0`. -/
theorem fderiv_ne_zero [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ) :
    fderiv a₂ a₄ a₆ p θ ≠ 0 := by
  have hroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    have := h.root; simpa [fval] using this
  have hΔ : (curve a₂ a₄ a₆).Δ.num
      = 16 * (-4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2
        + 18 * a₂ * a₄ * a₆) := by
    have hval : (curve a₂ a₄ a₆).Δ
        = ((16 * (-4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2
            + 18 * a₂ * a₄ * a₆) : ℤ) : ℚ) := by
      simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      push_cast; ring
    rw [hval, Rat.num_intCast]
  intro hfd
  apply h.discr
  rw [hΔ]
  have hfd' : 3 * θ ^ 2 + 2 * (a₂ : ZMod p) * θ + (a₄ : ZMod p) = 0 := by
    have := hfd; simpa [fderiv] using this
  push_cast
  linear_combination
    (16 * (-3 * θ ^ 2 - 2 * (a₂ : ZMod p) * θ + (a₂ : ZMod p) ^ 2 - 4 * (a₄ : ZMod p)) *
      (3 * θ ^ 2 + 2 * (a₂ : ZMod p) * θ + (a₄ : ZMod p))) * hfd'
    + (16 * (-4 * (a₂ : ZMod p) ^ 3 + 18 * (a₂ : ZMod p) * (a₄ : ZMod p)
      + 27 * (a₂ : ZMod p) * θ ^ 2 + 27 * (a₄ : ZMod p) * θ - 27 * (a₆ : ZMod p) + 27 * θ ^ 3))
        * hroot

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
  · -- Generic case.  The secant `P + Q = some x₃ y₃` gives three collinear points `P, Q, -(P+Q)`
    -- with `x`-coordinates `x₁, x₂, x₃ = addX x₁ x₂ (slope …)`.  When denominators survive
    -- reduction and `X₁ ≠ X₂` mod `p`, `lambda_map_add_of_good` closes it via T1a/T1b reduced
    -- mod `p` (including the three `2`-torsion sub-cases `Xᵢ = θ`).
    --
    -- The five remaining `sorry`s are the loci where the elementary reduction of the secant
    -- degenerates.  They are executable formalization content — deferred here, not a fundamental
    -- obstruction — sharing one theme: they need the good-reduction behavior of the group law
    -- where a point or the sum reduces to `O`, or two reduced points coincide.  The
    -- denominator-clearing method used for the good case does not reach them, because either
    -- `Rat.cast xᵢ` is *junk* once `(xᵢ.den : ZMod p) = 0` (the `→ O` patches: `x₁.num / x₁.den`
    -- casts to `x₁.num · 0 = 0`, not the true reduction), or the secant Vieta identities
    -- `reduced_addX` require both `x₁ ≠ x₂` over `ℚ` *and* `X₁ ≠ X₂` mod `p` and a non-tangent
    -- slope (the tangent/doubling patches).  Closing them needs a `padicValRat` argument tracking
    -- `p`-adic valuations through the secant/tangent formulas (e.g. `p ∣ x(P+Q).den` forces
    -- `v_p(x₁ − x₂) > 0`, i.e. `X₁ = X₂`), or equivalently a reduction homomorphism
    -- `E(ℚ) → E(𝔽ₚ)`, plus a `reduced_doubleX` counterpart of `reduced_addX` for the tangent
    -- slope.  See ticket T1d.
    by_cases hne : x₁ = x₂
    · -- PATCH (ℚ-tangent/doubling): `x₁ = x₂`.  Since `y₁² = y₂² = f(x₁)` and `y₁ ≠ negY x₂ y₂ =
      -- -y₂`, we have `y₁ = y₂`, i.e. `P = Q`; the goal is `λ(2P) = λP + λP = 0`.  Blocked: needs
      -- a `reduced_doubleX` (tangent-slope) lemma, and the sub-cases where `2P ≡ O` mod `p`
      -- (`P → O` or `P` `2`-torsion mod `p`) need `x(2P).den ≡ 0`, i.e. the reduction hom.
      sorry
    by_cases hdx1 : (x₁.den : ZMod p) = 0
    · -- PATCH (`P → O` mod `p`): `p ∣ w₁`, so `P` reduces to `O` of `E/𝔽ₚ` and `λP = 0`; the goal
      -- is `λ(P+Q) = λQ`, i.e. `X₃ = X₂` (as reduction data).  Blocked: `Rat.cast x₁` is junk,
      -- so `reduced_addX` is unavailable; `X₃ = X₂` is exactly `O + Q̄ = Q̄`, the reduction hom.
      sorry
    by_cases hdx2 : (x₂.den : ZMod p) = 0
    · -- PATCH (`Q → O` mod `p`): `p ∣ w₂`.  Symmetric to the previous; goal `λ(P+Q) = λP`.
      sorry
    by_cases hdx3 : (((curve a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curve a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0
    · -- PATCH (`P + Q → O` mod `p`): `p ∣ w₃`, so `λ(P+Q) = 0`; goal `λP + λQ = 0`.  Here
      -- `P̄ + Q̄ = O`, so `Q̄ = -P̄` and `X₁ = X₂`, forcing `λP = λQ` (equal reduced `x`), whence
      -- `λP + λQ = 0` in `ZMod 2`.  Blocked: deducing `X₁ = X₂` from `x(P+Q).den ≡ 0` is again
      -- the reduction hom (this branch also has `X₁ ≠ X₂` mod `p` still open below).
      sorry
    by_cases hbne : (x₁ : ZMod p) = (x₂ : ZMod p)
    · -- PATCH (tangent mod `p`): good denominators but `X₁ = X₂` mod `p`, so the reduced points
      -- coincide and the reduced slope is a tangent (doubling) slope, outside the secant Vieta
      -- relations `reduced_addX` (which need `X₁ ≠ X₂`).  Blocked: needs `reduced_doubleX` and,
      -- in the `Ȳ₁ = -Ȳ₂` sub-case (`P̄ = -Q̄`), the reduction hom to get `x(P+Q).den ≡ 0`.
      sorry
    -- GOOD REDUCTION (denominators survive, `X₁ ≠ X₂` mod `p`): fully proven, including the three
    -- `2`-torsion patches `Xᵢ = θ`, which are folded into `lambda_map_add_of_good`.
    exact lambda_map_add_of_good h h₁ h₂ hne hdx1 hdx2 hdx3 hbne

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
