/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Descent.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The collinearity identity (T1b)

A line `y = ℓx + m` that meets `E : y² = x³ + a₂x² + a₄x + a₆` in three points with
`x`-coordinates `x₁, x₂, x₃` gives the polynomial factorisation

  `x³ + a₂x² + a₄x + a₆ − (ℓx + m)² = (x − x₁)(x − x₂)(x − x₃)`,

since the cubic minus the squared line is monic of degree `3` with exactly those roots.
Evaluating at a root `θ` of `f(x) = x³ + a₂x² + a₄x + a₆` and using `f(θ) = 0` turns the
left side into `−(ℓθ + m)²`, so

  `(x₁ − θ)(x₂ − θ)(x₃ − θ) = (ℓθ + m)²`

is a perfect square.  This corollary is what ticket T1c feeds into the descent-character
additivity proof (the class of `x − θ` modulo squares is multiplicative along collinear
triples).

## Design

The factorisation is stated as an equation of values `∀ x, …` rather than of polynomials;
over an infinite field the two are equivalent, and the value form is exactly what the
`θ`-corollary needs.  Its content is the three Vieta relations between `(ℓ, m)` and the
symmetric functions of `x₁, x₂, x₃`, so both the identity and the corollary reduce to
`linear_combination`.  For the group-law application one only knows that two of the points
lie on the curve and the line and have distinct `x`-coordinates; `cubic_sub_lineSq_eq_prod_of_roots`
recovers the Vieta relations from that data over a field.

## Main declarations

* `ECCompute.cubic_sub_lineSq_eq_prod` — the collinearity identity from the Vieta relations.
* `ECCompute.prod_sub_theta_eq_lineSq` — the `θ`-evaluation corollary (perfect square).
* `ECCompute.cubic_sub_lineSq_eq_prod_of_roots` — the identity over a field from two points
  on the curve and line with distinct `x`-coordinates.
* `ECCompute.prod_sub_theta_eq_lineSq_of_roots` — the corollary from the same field data.
* `ECCompute.prod_sub_theta_eq_lineSq_zmod` — the corollary phrased with `fval` for the
  mod-`p` descent application.
-/

namespace ECCompute

section CommRing

variable {R : Type*} [CommRing R] (a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : R)

/-- **Collinearity identity.**  If `x₁, x₂, x₃` and the line `y = ℓx + m` satisfy the three
Vieta relations forced by `x³ + a₂x² + a₄x + a₆ − (ℓx + m)²` being the monic cubic with
roots `x₁, x₂, x₃`, then that cubic factors as `(x − x₁)(x − x₂)(x − x₃)` at every `x`. -/
theorem cubic_sub_lineSq_eq_prod
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆) (x : R) :
    x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ - (ℓ * x + m) ^ 2
      = (x - x₁) * (x - x₂) * (x - x₃) := by
  linear_combination x ^ 2 * hσ₁ - x * hσ₂ + hσ₃

/-- **The collinear triple meets `θ` in a square.**  Evaluating the collinearity identity at
a root `θ` of `f(x) = x³ + a₂x² + a₄x + a₆` gives `(x₁ − θ)(x₂ − θ)(x₃ − θ) = (ℓθ + m)²`. -/
theorem prod_sub_theta_eq_lineSq
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hθ : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 := by
  have key := cubic_sub_lineSq_eq_prod a₂ a₄ a₆ ℓ m x₁ x₂ x₃ hσ₁ hσ₂ hσ₃ θ
  linear_combination key - hθ

end CommRing

section Field

variable {F : Type*} [Field F] (a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : F)

/-- The Vieta relations for the line `y = ℓx + m` meeting `E` at `x₁, x₂, x₃`, recovered from
the two points `(x₁, ℓx₁ + m)` and `(x₂, ℓx₂ + m)` lying on the curve (with `x₁ ≠ x₂`) and the
group-law value `x₃ = ℓ² − a₂ − x₁ − x₂` for the third `x`-coordinate. -/
private theorem vieta_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : (ℓ * x₂ + m) ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆) :
    x₁ + x₂ + x₃ = ℓ ^ 2 - a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m ∧
        x₁ * x₂ * x₃ = m ^ 2 - a₆ := by
  have hQ : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ - ℓ ^ 2) * (x₁ + x₂) + (a₄ - 2 * ℓ * m) = 0 := by
    have hprod : (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a₂ - ℓ ^ 2) * (x₁ + x₂) + (a₄ - 2 * ℓ * m)) = 0 := by
      linear_combination h₂ - h₁
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  refine ⟨by rw [hx₃]; ring, by rw [hx₃]; linear_combination -hQ,
    by rw [hx₃]; linear_combination -h₁ - x₁ * hQ⟩

/-- **Collinearity identity over a field.**  Two points `(x₁, ℓx₁ + m)`, `(x₂, ℓx₂ + m)` on
`E` with `x₁ ≠ x₂` and the group-law third coordinate `x₃ = ℓ² − a₂ − x₁ − x₂` factor the
cubic-minus-line-squared as `(x − x₁)(x − x₂)(x − x₃)`. -/
theorem cubic_sub_lineSq_eq_prod_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : (ℓ * x₂ + m) ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆) (x : F) :
    x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ - (ℓ * x + m) ^ 2
      = (x - x₁) * (x - x₂) * (x - x₃) := by
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots a₂ a₄ a₆ ℓ m x₁ x₂ x₃ hne hx₃ h₁ h₂
  exact cubic_sub_lineSq_eq_prod a₂ a₄ a₆ ℓ m x₁ x₂ x₃ hσ₁ hσ₂ hσ₃ x

/-- **The collinear triple meets `θ` in a square, over a field.**  From two points on `E` and
the line (distinct `x`), together with `f(θ) = 0`, the third value `x₃ = ℓ² − a₂ − x₁ − x₂`
gives `(x₁ − θ)(x₂ − θ)(x₃ − θ) = (ℓθ + m)²`. -/
theorem prod_sub_theta_eq_lineSq_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : (ℓ * x₂ + m) ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hθ : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 := by
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := vieta_of_roots a₂ a₄ a₆ ℓ m x₁ x₂ x₃ hne hx₃ h₁ h₂
  exact prod_sub_theta_eq_lineSq a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ hσ₁ hσ₂ hσ₃ hθ

end Field

/-- **The `θ`-corollary for the mod-`p` descent.**  Phrased with `fval` so that the root
hypothesis is exactly `DescentHyp.root`: at a root `θ` of `f` mod `p`, a collinear triple
`x₁, x₂, x₃` on the line `y = ℓx + m` satisfies `(x₁ − θ)(x₂ − θ)(x₃ − θ) = (ℓθ + m)²`, a
square in `ZMod p`. -/
theorem prod_sub_theta_eq_lineSq_zmod (a₂ a₄ a₆ : ℤ) (p : ℕ) (ℓ m x₁ x₂ x₃ θ : ZMod p)
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - (a₂ : ZMod p))
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = (a₄ : ZMod p) - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - (a₆ : ZMod p))
    (hroot : fval a₂ a₄ a₆ p θ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 :=
  prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₁ x₂ x₃ θ
    hσ₁ hσ₂ hσ₃ (by simpa only [fval] using hroot)

end ECCompute
