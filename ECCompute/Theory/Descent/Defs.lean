/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic

/-!
# The descent character: basic definitions

For an elliptic curve `E : y² = f(x)` with `f = x³ + a₂x² + a₄x + a₆` a monic integral cubic
of non-zero discriminant, a prime `p ∤ 6Δ`, and a root `θ ∈ 𝔽ₚ` of `f`, this file defines the
*descent character* `λ_{p,θ} : E(ℚ) → ZMod 2` as a raw function, together with the arithmetic
hypotheses `DescentHyp`.

For a point `P = (x, y) = (u/w², v/w³)` on `E`, set `α := u - θ·w² = x.num - θ·x.den` in
`ZMod p` (when `p ∤ w`, i.e. `(x.den : ZMod p) ≠ 0`). Then `λ(O) = 0`; `λ(P) = 0` if `p ∣ w`;
`λ(P) = ψ_p(f'(θ))` if `α = 0` (the tangent case); and `λ(P) = ψ_p(α)` otherwise, where
`ψ_p : ZMod p → ZMod 2` is the Legendre symbol (`0` on squares, `1` on non-squares).

## Main declarations

* `ECCompute.psi`: the Legendre symbol into `ZMod 2`.
* `ECCompute.curve`: the Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆`.
* `ECCompute.lambda`: the raw function `E(ℚ) → ZMod 2`.
* `ECCompute.DescentHyp`: the arithmetic hypotheses `p ∤ 6Δ`, `f(θ) ≡ 0`.
-/

public section

open WeierstrassCurve

namespace WeierstrassCurve

/-- The affine `2`-torsion points of `W`: the points `P` with `P + P = 0`. -/
@[expose] def twoTorsionPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point :=
  {P | P + P = 0}

@[simp]
lemma mem_twoTorsionPoints {W : WeierstrassCurve ℚ} {P : W.toAffine.Point} :
    P ∈ W.twoTorsionPoints ↔ P + P = 0 := Iff.rfl

end WeierstrassCurve

namespace ECCompute

open Classical in
/-- The Legendre symbol pushed into `(ZMod 2, +)`: `0` on squares (including `0`), `1` on
non-squares. -/
@[expose] noncomputable def psi (p : ℕ) (a : ZMod p) : ZMod 2 :=
  if IsSquare a then 0 else 1

/-- The Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ`, i.e. `a₁ = a₃ = 0`. -/
@[expose] def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

/-- The affine equation of `curve a₂ a₄ a₆` in cleared form. -/
@[grind →]
theorem equation_curve {x y : ℚ} (h : (curve a₂ a₄ a₆).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by
  grind [Affine.equation_iff, curve]

/-- The value `f(θ) = θ³ + a₂θ² + a₄θ + a₆` in `ZMod p`. -/
@[expose] def fval (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) : ZMod p :=
  θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆

/-- The value `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`. -/
@[expose] def fderiv (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) : ZMod p :=
  3 * θ ^ 2 + 2 * a₂ * θ + a₄

/-- The descent character as a raw function. -/
@[expose] noncomputable def lambda (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) :
    (curve a₂ a₄ a₆).toAffine.Point → ZMod 2
  | .zero => 0
  | .some x _ _ =>
    if (x.den : ZMod p) = 0 then 0
    else
      let α : ZMod p := x.num - θ * x.den
      if α = 0 then psi p (fderiv a₂ a₄ p θ) else psi p α

@[simp, grind =]
theorem lambda_zero (θ : ZMod p) : lambda a₂ a₄ a₆ p θ 0 = 0 := rfl

/-! ### The hypotheses of the descent lemma

`p ∤ 6Δ` is expressed as `p` prime, `p ∤ 6` (so `p ≠ 2, 3`), and the integer discriminant a
unit mod `p` (the coefficients being integers, `Δ` is an integer, so `(curve …).Δ.num` is it). -/

/-- Arithmetic hypotheses of the descent lemma for the label `(p, θ)`. -/
structure DescentHyp (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) : Prop where
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `p ∤ 6` (equivalently `p ≠ 2` and `p ≠ 3`). -/
  ne_six : ¬ p ∣ 6
  /-- `p ∤ Δ`: the (integer) discriminant is invertible mod `p`. -/
  discr : ((curve a₂ a₄ a₆).Δ.num : ZMod p) ≠ 0
  /-- `θ` is a root of `f` mod `p`, i.e. `f(θ) ≡ 0`. -/
  root : fval a₂ a₄ a₆ p θ = 0

attribute [grind →] DescentHyp.discr DescentHyp.root

end ECCompute
