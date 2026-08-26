/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character

import Mathlib.Tactic.LinearCombination

/-!
# The collinearity identity

A line `y = ℓx + m` meeting `E : y² = x³ + a₂x² + a₄x + a₆` in three points with
`x`-coordinates `x₁, x₂, x₃` gives `x³ + a₂x² + a₄x + a₆ - (ℓx + m)² = (x - x₁)(x - x₂)(x - x₃)`.
Evaluating at a root `θ` of `f(x) = x³ + a₂x² + a₄x + a₆` yields
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`, a perfect square, used in the descent-character
additivity proof.

The factorization is stated as an equation of values `∀ x, …`, the form the `θ`-corollary needs.
Its content is the three Vieta relations between `(ℓ, m)` and the symmetric functions of
`x₁, x₂, x₃`.

## Main declarations

* `ECCompute.cubic_sub_lineSq_eq_prod`: the collinearity identity from the Vieta relations.
* `ECCompute.prod_sub_theta_eq_lineSq`: the `θ`-evaluation corollary (perfect square).
* `ECCompute.prod_sub_theta_eq_lineSq_zmod`: the corollary phrased with `fval` for the
  mod-`p` descent application.
-/

namespace ECCompute

section CommRing

variable {R : Type*} [CommRing R] (a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : R)

/-- If `x₁, x₂, x₃` and the line `y = ℓx + m` satisfy the three Vieta relations, the cubic
`x³ + a₂x² + a₄x + a₆ - (ℓx + m)²` factors as `(x - x₁)(x - x₂)(x - x₃)` at every `x`. -/
theorem cubic_sub_lineSq_eq_prod
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆) {x : R} :
    x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ - (ℓ * x + m) ^ 2 = (x - x₁) * (x - x₂) * (x - x₃) := by grind

/-- Evaluating the collinearity identity at a root `θ` of `f(x) = x³ + a₂x² + a₄x + a₆` gives
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`. -/
public theorem prod_sub_theta_eq_lineSq
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hθ : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 := by grind [cubic_sub_lineSq_eq_prod]

/-- If the line `y = ℓx + m` is tangent to `E` at `(x₁, ℓx₁ + m)` (point on curve `hpt`,
slope condition `f'(x₁) = 2ℓ(ℓx₁ + m)` as `htan`), then `x₁` is a double root and the Vieta
relations hold for the triple `x₁, x₁, x₃` with `x₃ = ℓ² - a₂ - 2x₁`. Doubling analogue of
`vieta_of_roots`. -/
public theorem vieta_of_double_root
    (hpt : (ℓ * x₁ + m) ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (htan : 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ = 2 * ℓ * (ℓ * x₁ + m))
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - 2 * x₁) :
    x₁ + x₁ + x₃ = ℓ ^ 2 - a₂ ∧
      x₁ * x₁ + x₁ * x₃ + x₁ * x₃ = a₄ - 2 * ℓ * m ∧
        x₁ * x₁ * x₃ = m ^ 2 - a₆ := by grind

end CommRing

section Field

variable {F : Type*} [Field F] (a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : F)

/-- The Vieta relations for the line `y = ℓx + m` meeting `E` at `x₁, x₂, x₃`, recovered from
the two points `(x₁, ℓx₁ + m)` and `(x₂, ℓx₂ + m)` lying on the curve (with `x₁ ≠ x₂`) and the
group-law value `x₃ = ℓ² - a₂ - x₁ - x₂` for the third `x`-coordinate. -/
public theorem vieta_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : (ℓ * x₂ + m) ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆) :
    x₁ + x₂ + x₃ = ℓ ^ 2 - a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m ∧ x₁ * x₂ * x₃ = m ^ 2 - a₆ := by
  grind (ringSteps := 200000)

/-- If `θ` is a root of `f` and one collinear `x`-coordinate equals `θ` (here `x₁ = θ`), then
`f'(θ) = (x₂ - θ)(x₃ - θ)`. Analogue of `prod_sub_theta_eq_lineSq` for the tangent (`2`-torsion
mod `p`) branch, where the factor `X_i - θ` is replaced by `f'(θ)`. -/
public theorem fderiv_eq_prod
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hθ : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0) (h1 : x₁ = θ) :
    fderiv a₂ a₄ θ = (x₂ - θ) * (x₃ - θ) := by grind [fderiv, cubic_sub_lineSq_eq_prod]

end Field

/-- The `θ`-corollary phrased with `fval` so the root hypothesis is exactly `DescentHyp.root`:
at a root `θ` of `f` mod `p`, a collinear triple on `y = ℓx + m` satisfies
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`, a square in `ZMod p`. -/
public theorem prod_sub_theta_eq_lineSq_zmod {a₂ a₄ a₆ : ℤ} (p : ℕ) (ℓ m x₁ x₂ x₃ θ : ZMod p)
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hroot : fval a₂ a₄ a₆ θ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 :=
  prod_sub_theta_eq_lineSq (a₂ : ZMod p) (a₄ : ZMod p) (a₆ : ZMod p) ℓ m x₁ x₂ x₃ θ
    hσ₁ hσ₂ hσ₃ (by simpa only [fval] using hroot)

end ECCompute
