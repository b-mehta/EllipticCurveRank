/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
public import ECCompute.Theory.Model

import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The descent character

For an elliptic curve `E : y² = f(x)` with `f = x³ + a₂x² + a₄x + a₆` a monic integral cubic
of non-zero discriminant, a prime `p ∤ 6Δ`, and a root `θ ∈ 𝔽ₚ` of `f`, this file defines the
*descent character* `λ_{p,θ} : E(ℚ) → ZMod 2` as a raw function, together with the arithmetic
hypotheses `DescentHyp`, the collinearity identity behind its additivity, and the arithmetic of
the Legendre symbol `ψ_p`.

For a point `P = (x, y) = (u/w², v/w³)` on `E`, set `α := u - θ·w² = x.num - θ·x.den` in
`ZMod p` (when `p ∤ w`, i.e. `(x.den : ZMod p) ≠ 0`). Then `λ(O) = 0`; `λ(P) = 0` if `p ∣ w`;
`λ(P) = ψ_p(f'(θ))` if `α = 0` (the tangent case); and `λ(P) = ψ_p(α)` otherwise, where
`ψ_p : ZMod p → ZMod 2` is the Legendre symbol (`0` on squares, `1` on non-squares).

## Main declarations

* `ECCompute.psi`: the Legendre symbol into `ZMod 2`; `ECCompute.lambda`: the raw character.
* `ECCompute.DescentHyp`: the arithmetic hypotheses `p ∤ 6Δ`, `f(θ) ≡ 0`.
* `ECCompute.prod_sub_theta_eq_lineSq`: the collinearity identity `(x₁-θ)(x₂-θ)(x₃-θ) = (ℓθ+m)²`.
* `ECCompute.psi_mul`: `ψ_p` turns products into sums on nonzero elements.
* `ECCompute.psi_collinear`, `ECCompute.fderiv_ne_zero`: the collinear-sum and simple-root facts.
-/

open WeierstrassCurve

namespace ECCompute

section

open Classical in
/-- The Legendre symbol pushed into `(ZMod 2, +)`: `0` on squares (including `0`), `1` on
non-squares. -/
@[expose] public noncomputable def psi (p : ℕ) (a : ZMod p) : ZMod 2 := if IsSquare a then 0 else 1

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

/-- The value `f(θ) = θ³ + a₂θ² + a₄θ + a₆`. -/
@[expose] public def fval {R : Type*} [CommRing R] (a₂ a₄ a₆ θ : R) : R :=
  θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆

/-- The value `f'(θ) = 3θ² + 2a₂θ + a₄`. -/
@[expose] public def fderiv {R : Type*} [CommRing R] (a₂ a₄ θ : R) : R :=
  3 * θ ^ 2 + 2 * a₂ * θ + a₄

/-- The descent character as a raw function. -/
@[expose] public noncomputable def lambda (θ : ZMod p) :
    (curve a₂ a₄ a₆).toAffine.Point → ZMod 2
  | .zero => 0
  | .some x _ _ =>
    if (x.den : ZMod p) = 0 then 0
    else
      let α : ZMod p := x.num - θ * x.den
      if α = 0 then psi p (fderiv (R := ZMod p) a₂ a₄ θ) else psi p α

@[simp, grind =]
public theorem lambda_zero {θ : ZMod p} :
    lambda θ (0 : (curve a₂ a₄ a₆).toAffine.Point) = 0 := rfl

/-! ### The hypotheses of the descent lemma

`p ∤ 6Δ` is expressed as `p` prime, `p ∤ 6` (so `p ≠ 2, 3`), and the integer discriminant a
unit mod `p` (the coefficients being integers, `Δ` is an integer, so `(curve …).Δ.num` is it). -/

/-- Arithmetic hypotheses of the descent lemma for the label `(p, θ)`. -/
public structure DescentHyp (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) : Prop where
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `p ∤ 6` (equivalently `p ≠ 2` and `p ≠ 3`). -/
  ne_six : ¬ p ∣ 6
  /-- `p ∤ Δ`: the (integer) discriminant is invertible mod `p`. -/
  discr : ((curve a₂ a₄ a₆).Δ.num : ZMod p) ≠ 0
  /-- `θ` is a root of `f` mod `p`, i.e. `f(θ) ≡ 0`. -/
  root : fval (a₂ : ZMod p) a₄ a₆ θ = 0

attribute [grind →] DescentHyp.discr DescentHyp.root

end

/-! ### The collinearity identity

A line `y = ℓx + m` meeting `E` in three points with `x`-coordinates `x₁, x₂, x₃` gives
`f(x) - (ℓx + m)² = (x - x₁)(x - x₂)(x - x₃)`. At a root `θ` of `f` this yields
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`, a perfect square, used in the additivity proof. -/

section CommRing

variable {R : Type*} [CommRing R] {a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : R}

/-- If `x₁, x₂, x₃` and the line `y = ℓx + m` satisfy the three Vieta relations, the cubic
`x³ + a₂x² + a₄x + a₆ - (ℓx + m)²` factors as `(x - x₁)(x - x₂)(x - x₃)` at every `x`. -/
theorem cubic_sub_lineSq_eq_prod
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆) {x : R} :
    fval a₂ a₄ a₆ x - (ℓ * x + m) ^ 2 = (x - x₁) * (x - x₂) * (x - x₃) := by grind [fval]

/-- Evaluating the collinearity identity at a root `θ` of `f(x) = x³ + a₂x² + a₄x + a₆` gives
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`. -/
public theorem prod_sub_theta_eq_lineSq
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hθ : fval a₂ a₄ a₆ θ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 := by grind [fval, cubic_sub_lineSq_eq_prod]

/-- If the line `y = ℓx + m` is tangent to `E` at `(x₁, ℓx₁ + m)` (point on curve `hpt`,
slope condition `f'(x₁) = 2ℓ(ℓx₁ + m)` as `htan`), then `x₁` is a double root and the Vieta
relations hold for the triple `x₁, x₁, x₃` with `x₃ = ℓ² - a₂ - 2x₁`. Doubling analogue of
`vieta_of_roots`. -/
public theorem vieta_of_double_root
    (hpt : (ℓ * x₁ + m) ^ 2 = fval a₂ a₄ a₆ x₁)
    (htan : fderiv a₂ a₄ x₁ = 2 * ℓ * (ℓ * x₁ + m))
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - 2 * x₁) :
    x₁ + x₁ + x₃ = ℓ ^ 2 - a₂ ∧
      x₁ * x₁ + x₁ * x₃ + x₁ * x₃ = a₄ - 2 * ℓ * m ∧
        x₁ * x₁ * x₃ = m ^ 2 - a₆ := by grind [fval, fderiv]

end CommRing

section Field

variable {F : Type*} [Field F] {a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : F}

/-- The Vieta relations for the line `y = ℓx + m` meeting `E` at `x₁, x₂, x₃`, recovered from
the two points `(x₁, ℓx₁ + m)` and `(x₂, ℓx₂ + m)` lying on the curve (with `x₁ ≠ x₂`) and the
group-law value `x₃ = ℓ² - a₂ - x₁ - x₂` for the third `x`-coordinate. -/
public theorem vieta_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = fval a₂ a₄ a₆ x₁)
    (h₂ : (ℓ * x₂ + m) ^ 2 = fval a₂ a₄ a₆ x₂) :
    x₁ + x₂ + x₃ = ℓ ^ 2 - a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m ∧ x₁ * x₂ * x₃ = m ^ 2 - a₆ := by
  grind (ringSteps := 200000) [fval]

/-- If `θ` is a root of `f` and one collinear `x`-coordinate equals `θ` (here `x₁ = θ`), then
`f'(θ) = (x₂ - θ)(x₃ - θ)`. Analogue of `prod_sub_theta_eq_lineSq` for the tangent (`2`-torsion
mod `p`) branch, where the factor `X_i - θ` is replaced by `f'(θ)`. -/
public theorem fderiv_eq_prod (ℓ m : F)
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hθ : fval a₂ a₄ a₆ θ = 0) (h1 : x₁ = θ) :
    fderiv a₂ a₄ θ = (x₂ - θ) * (x₃ - θ) := by grind [fval, fderiv, cubic_sub_lineSq_eq_prod]

end Field

/-- The `θ`-corollary phrased with `fval` so the root hypothesis is exactly `DescentHyp.root`:
at a root `θ` of `f` mod `p`, a collinear triple on `y = ℓx + m` satisfies
`(x₁ - θ)(x₂ - θ)(x₃ - θ) = (ℓθ + m)²`, a square in `ZMod p`. -/
theorem prod_sub_theta_eq_lineSq_zmod {a₂ a₄ a₆ : ℤ} {p : ℕ} {ℓ m x₁ x₂ x₃ θ : ZMod p}
    (hσ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂)
    (hσ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆)
    (hroot : fval (a₂ : ZMod p) a₄ a₆ θ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 :=
  prod_sub_theta_eq_lineSq hσ₁ hσ₂ hσ₃ (by simpa only [fval] using hroot)

/-! ### The Legendre character `ψ_p` is a homomorphism away from zero

On the nonzero elements of `ZMod p` (`p` an odd prime), `ψ_p` is the quadratic-residue character
transported along `{±1} ≅ ZMod 2`, hence additive: `ψ_p(ab) = ψ_p a + ψ_p b`. The simple-root
fact `fderiv_ne_zero` closes the section. -/

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

section Psi

variable {a b : ZMod p}

/-- `ψ_p` vanishes on squares. -/
public theorem psi_of_isSquare (ha : IsSquare a) : psi p a = 0 := if_pos ha

/-- On the nonzero elements of `ZMod p` (`p` prime), `ψ_p` turns products into sums:
`ψ_p(ab) = ψ_p a + ψ_p b`. -/
public theorem psi_mul (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    psi p (a * b) = psi p a + psi p b := by
  have : Fact p.Prime := ⟨hp⟩
  -- `IsSquare (a*b) ↔ (IsSquare a ↔ IsSquare b)` on nonzero elements, via `quadraticChar`.
  have key : IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    rw [← quadraticChar_one_iff_isSquare hab, ← quadraticChar_one_iff_isSquare ha,
      ← quadraticChar_one_iff_isSquare hb, map_mul]
    grind [quadraticChar_dichotomy]
  grind [psi]

/-- Multiplying by a nonzero square does not change `ψ_p`. -/
public theorem psi_mul_sq (hp : p.Prime) (hb : b ≠ 0) :
    psi p (b ^ 2 * a) = psi p a := by
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne a 0 with rfl | ha
  · rw [mul_zero]
  · rw [psi_mul hp (pow_ne_zero 2 hb) ha, psi_of_isSquare ⟨b, by ring⟩, zero_add]

end Psi

variable {θ : ZMod p}

/-- If `X₁, X₂, X₃` are the reduced `x`-coordinates of three collinear points on `E` (via the
Vieta relations of `y = ℓx + m`), all distinct from the root `θ`, then
`ψ_p (X₁ - θ) + ψ_p (X₂ - θ) + ψ_p (X₃ - θ) = 0`. -/
public theorem psi_collinear (hp : p.Prime) {ℓ m X₁ X₂ X₃ : ZMod p}
    (hσ₁ : X₁ + X₂ + X₃ = ℓ ^ 2 - a₂)
    (hσ₂ : X₁ * X₂ + X₁ * X₃ + X₂ * X₃ = a₄ - 2 * ℓ * m)
    (hσ₃ : X₁ * X₂ * X₃ = m ^ 2 - a₆)
    (hroot : fval (a₂ : ZMod p) a₄ a₆ θ = 0)
    (hX₁ : X₁ ≠ θ) (hX₂ : X₂ ≠ θ) (hX₃ : X₃ ≠ θ) :
    psi p (X₁ - θ) + psi p (X₂ - θ) + psi p (X₃ - θ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hprod := prod_sub_theta_eq_lineSq_zmod hσ₁ hσ₂ hσ₃ hroot
  have h1 : X₁ - θ ≠ 0 := sub_ne_zero.mpr hX₁
  have h2 : X₂ - θ ≠ 0 := sub_ne_zero.mpr hX₂
  have h3 : X₃ - θ ≠ 0 := sub_ne_zero.mpr hX₃
  have hpm : psi p ((X₁ - θ) * (X₂ - θ) * (X₃ - θ)) = 0 := by
    rw [hprod]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
  rwa [psi_mul hp (mul_ne_zero h1 h2) h3, psi_mul hp h1 h2] at hpm

/-- The root `θ` of `f` is simple, so `f'(θ) ≠ 0`. Uses the descent hypotheses `DescentHyp`
(`p ∤ 6Δ`). -/
public theorem fderiv_ne_zero (h : DescentHyp a₂ a₄ a₆ p θ) :
    fderiv (a₂ : ZMod p) a₄ θ ≠ 0 := by
  have hroot : θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ = 0 := by simpa [fval] using h.root
  intro hfd
  apply h.discr
  rw [curve_Δ_num]
  simp only [discrInt]
  grind [fderiv]

end ECCompute
