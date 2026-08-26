/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Defs

import ECCompute.Theory.Descent.Collinearity
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The Legendre character `ψ_p` and the simple-root fact (shared base)

The `ψ_p`-arithmetic and the simple-root fact `fderiv_ne_zero`, shared between the two sides of
the descent factorization `λ = εpFinite ∘ redP`: `ECCompute.Descent` (the rational character
`λ`) and `ECCompute.Descent.Reduction.EpsFinite` (the finite-field character `εpFinite`).

## Main declarations

* `ECCompute.psi_of_isSquare`: `ψ_p` vanishes on squares.
* `ECCompute.psi_mul_sq`: multiplying by a nonzero square does not change `ψ_p`.
* `ECCompute.psi_mul`: `ψ_p` turns products into sums on nonzero elements.
* `ECCompute.psi_collinear`: `ψ_p` sums to zero on a collinear triple.
* `ECCompute.fderiv_ne_zero`: `f'(θ) ≠ 0` (the root `θ` is simple, from `p ∤ 6Δ`).
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

/-! ### The Legendre character `ψ_p` is a homomorphism away from zero

On the nonzero elements of `ZMod p` (`p` an odd prime), `ψ_p` is the quadratic-residue character
transported along `{±1} ≅ ZMod 2`, hence additive: `ψ_p(ab) = ψ_p a + ψ_p b`. -/

section Psi

/-- `ψ_p` vanishes on squares. -/
public theorem psi_of_isSquare {a : ZMod p} (ha : IsSquare a) : psi p a = 0 :=
  if_pos ha

/-- Multiplying by a nonzero square does not change `ψ_p`. -/
public theorem psi_mul_sq [Fact p.Prime] {a w : ZMod p} (hw : w ≠ 0) :
    psi p (w ^ 2 * a) = psi p a := by
  have hiff : IsSquare (w ^ 2 * a) ↔ IsSquare a :=
    ⟨fun ⟨s, hs⟩ ↦ ⟨s / w, by grind⟩, fun ⟨r, hr⟩ ↦ ⟨w * r, by rw [hr]; ring⟩⟩
  unfold psi
  rw [hiff]

/-- On the nonzero elements of `ZMod p` (`p` prime), `ψ_p` turns products into sums:
`ψ_p(ab) = ψ_p a + ψ_p b`. -/
public theorem psi_mul (hp : p.Prime) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
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

/-- If `X₁, X₂, X₃` are the reduced `x`-coordinates of three collinear points on `E` (via the
Vieta relations of `y = ℓx + m`), all distinct from the root `θ`, then
`ψ_p (X₁ - θ) + ψ_p (X₂ - θ) + ψ_p (X₃ - θ) = 0`. -/
public theorem psi_collinear (hp : p.Prime) {θ ℓ m X₁ X₂ X₃ : ZMod p}
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

/-- The root `θ` of `f` is simple, so `f'(θ) ≠ 0`. Uses the descent hypotheses `DescentHyp`
(`p ∤ 6Δ`). -/
public theorem fderiv_ne_zero {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ) :
    fderiv a₂ a₄ p θ ≠ 0 := by
  have hroot : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0 := by simpa [fval] using h.root
  have hΔ : (curve a₂ a₄ a₆).Δ.num
      = 16 * (-4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2
        + 18 * a₂ * a₄ * a₆) := by
    simp [curve, Δ, b₂, b₄, b₆, b₈]
    norm_cast
    grind
  intro hfd
  apply h.discr
  rw [hΔ]
  grind [fderiv]

end ECCompute
