/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Theory.Descent.Collinearity
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The Legendre character `ψ_p` and the simple-root fact (shared base)

The `ψ_p`-arithmetic and the simple-root fact `fderiv_ne_zero`, shared between the two sides of
the descent factorization `λ = εp_finite ∘ red_p`: `ECCompute.Descent` (the rational character
`λ`) and `ECCompute.Descent.Reduction.EpsFinite` (the finite-field character `εp_finite`).

## Main declarations

* `ECCompute.psi_of_isSquare`: `ψ_p` vanishes on squares.
* `ECCompute.psi_mul_sq`: multiplying by a nonzero square does not change `ψ_p`.
* `ECCompute.psi_mul`: `ψ_p` turns products into sums on nonzero elements.
* `ECCompute.psi_collinear`: `ψ_p` sums to zero on a collinear triple.
* `ECCompute.fderiv_ne_zero`: `f'(θ) ≠ 0` (the root `θ` is simple, from `p ∤ 6Δ`).
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-! ### The Legendre character `ψ_p` is a homomorphism away from zero

On the nonzero elements of `ZMod p` (`p` an odd prime), `ψ_p` is the quadratic-residue character
transported along `{±1} ≅ ZMod 2`, hence additive: `ψ_p(ab) = ψ_p a + ψ_p b`. Proved via
`quadraticChar`. -/

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
      exact ⟨s / w, by grind⟩
    · rintro ⟨r, rfl⟩
      exact ⟨w * r, by ring⟩
  unfold psi
  rw [hiff]

/-- On the nonzero elements of `ZMod p` (`p` prime), `ψ_p` turns products into sums:
`ψ_p(ab) = ψ_p a + ψ_p b`. -/
theorem psi_mul (hp : p.Prime) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    psi p (a * b) = psi p a + psi p b := by
  have : Fact p.Prime := ⟨hp⟩
  -- `IsSquare (a*b) ↔ (IsSquare a ↔ IsSquare b)` on nonzero elements, via `quadraticChar`.
  have key : IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    rw [← quadraticChar_one_iff_isSquare hab, ← quadraticChar_one_iff_isSquare ha,
      ← quadraticChar_one_iff_isSquare hb, map_mul]
    grind [quadraticChar_dichotomy]
  grind [psi]

end Psi

variable {a₂ a₄ a₆ p}

/-- If `X₁, X₂, X₃` are the reduced `x`-coordinates of three collinear points on `E` (via the
Vieta relations of `y = ℓx + m`), all distinct from the root `θ`, then the `ψ_p`-values sum to
zero: collinearity makes `(X₁-θ)(X₂-θ)(X₃-θ)` a square, and `ψ_p` is additive on the nonzero
factors. -/
theorem psi_collinear (hp : p.Prime) {θ ℓ m X₁ X₂ X₃ : ZMod p}
    (hσ₁ : X₁ + X₂ + X₃ = ℓ ^ 2 - (a₂ : ZMod p))
    (hσ₂ : X₁ * X₂ + X₁ * X₃ + X₂ * X₃ = (a₄ : ZMod p) - 2 * ℓ * m)
    (hσ₃ : X₁ * X₂ * X₃ = m ^ 2 - (a₆ : ZMod p))
    (hroot : fval a₂ a₄ a₆ p θ = 0)
    (hX₁ : X₁ ≠ θ) (hX₂ : X₂ ≠ θ) (hX₃ : X₃ ≠ θ) :
    psi p (X₁ - θ) + psi p (X₂ - θ) + psi p (X₃ - θ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hprod := prod_sub_theta_eq_lineSq_zmod a₂ a₄ a₆ p ℓ m X₁ X₂ X₃ θ hσ₁ hσ₂ hσ₃ hroot
  have h1 : X₁ - θ ≠ 0 := sub_ne_zero.mpr hX₁
  have h2 : X₂ - θ ≠ 0 := sub_ne_zero.mpr hX₂
  have h3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr hX₃
  have hpm : psi p ((X₁ - θ) * (X₂ - θ) * (X₃ - θ)) = 0 := by
    rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
  rwa [psi_mul hp (mul_ne_zero h1 h2) h3, psi_mul hp h1 h2] at hpm

/-- Since `p ∤ 6Δ` and `θ` is a root of `f`, `θ` is a *simple* root, so `f'(θ) ≠ 0`:
`disc(f) = f'(θ)² · (B² - 4C)` for the complementary factor `x² + Bx + C = f(x)/(x - θ)`, and
`Δ = 16·disc(f)`, so `f'(θ) = 0` would force `Δ ≡ 0`. -/
theorem fderiv_ne_zero [Fact p.Prime] {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ) :
    fderiv a₂ a₄ p θ ≠ 0 := by
  have hroot : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := by
    simpa [fval] using h.root
  have hΔ : (curve a₂ a₄ a₆).Δ.num
      = 16 * (-4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2
        + 18 * a₂ * a₄ * a₆) := by
    have hval : (curve a₂ a₄ a₆).Δ
        = ((16 * (-4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2
            + 18 * a₂ * a₄ * a₆) : ℤ) : ℚ) := by
      simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      grind [pow_two]
    rw [hval, Rat.num_intCast]
  intro hfd
  apply h.discr
  rw [hΔ]
  have hfd' : 3 * θ ^ 2 + 2 * (a₂ : ZMod p) * θ + (a₄ : ZMod p) = 0 := by
    simpa [fderiv] using hfd
  push_cast
  linear_combination
    (16 * (-3 * θ ^ 2 - 2 * (a₂ : ZMod p) * θ + (a₂ : ZMod p) ^ 2 - 4 * (a₄ : ZMod p)) *
      (3 * θ ^ 2 + 2 * (a₂ : ZMod p) * θ + (a₄ : ZMod p))) * hfd'
    + (16 * (-4 * (a₂ : ZMod p) ^ 3 + 18 * (a₂ : ZMod p) * (a₄ : ZMod p)
      + 27 * (a₂ : ZMod p) * θ ^ 2 + 27 * (a₄ : ZMod p) * θ - 27 * (a₆ : ZMod p) + 27 * θ ^ 3))
        * hroot

end ECCompute
