import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic

/-!
# The descent character: basic definitions (T1)

For an elliptic curve `E : y² = f(x)` with `f = x³ + a₂x² + a₄x + a₆` a monic integral
cubic of non-zero discriminant, a prime `p ∤ 6Δ`, and a root `θ ∈ 𝔽ₚ` of `f`, this file
defines the *descent character*

  `λ_{p,θ} : E(ℚ) → ZMod 2`

as a raw function, together with the arithmetic hypotheses `DescentHyp`.  The additivity
theorem `lambda_map_add` and the `AddMonoidHom` packaging live in `ECCompute.Descent`, which
imports this file together with the two supporting lemmas T1a (`DenominatorSquare`) and T1b
(`Collinearity`).  Splitting the definitions here breaks the import cycle those two files
would otherwise create with `ECCompute.Descent`.

## Mathematical definition

Write a rational `x` in lowest terms.  Mathlib gives `x.num : ℤ` and `x.den : ℕ` with
`gcd(num, den) = 1`.  For a point `P = (x, y)` on `E` the standard theory shows
`x.den = w²` is a perfect square (and `x.num = u`), so the point is `(u/w², v/w³)`.  We
never need that fact to *define* `λ`, because dividing by the square `w²` does not change a
Legendre symbol.  Concretely, modulo `p` (when `p ∤ w`, i.e. `(x.den : ZMod p) ≠ 0`):

  `α := u − θ·w² = x.num − θ·x.den   (in ZMod p)`.

Then
* `λ(O) = 0`;
* `λ(P) = 0`                          if `p ∣ w`   (i.e. `(x.den : ZMod p) = 0`);
* `λ(P) = ψ_p(f'(θ))`                 if `α = 0`   (`u ≡ θw²`, the tangent case);
* `λ(P) = ψ_p(α)`                     otherwise,
where `ψ_p : ZMod p → ZMod 2` sends squares (and `0`) to `0` and non-squares to `1` — the
Legendre symbol pushed into `(ZMod 2, +)`.

## Main declarations

* `ECCompute.psi`        — the Legendre symbol into `ZMod 2`.
* `ECCompute.curve`      — the Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆`.
* `ECCompute.lambda`     — the raw function `E(ℚ) → ZMod 2`.
* `ECCompute.DescentHyp` — the arithmetic hypotheses `p ∤ 6Δ`, `f(θ) ≡ 0`.
-/

open WeierstrassCurve

namespace ECCompute

open scoped Classical

/-- The Legendre symbol pushed into `(ZMod 2, +)`: `0` on squares (including `0`), `1` on
non-squares.  For a prime `p ∤ a`, this is `0` iff `a` is a quadratic residue mod `p`. -/
noncomputable def psi (p : ℕ) (a : ZMod p) : ZMod 2 :=
  if IsSquare a then 0 else 1

/-- The Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆` over `ℚ`, i.e. `a₁ = a₃ = 0`. -/
def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable (a₂ a₄ a₆ : ℤ) (p : ℕ)

/-- The value `f(θ) = θ³ + a₂θ² + a₄θ + a₆` in `ZMod p`. -/
def fval (θ : ZMod p) : ZMod p :=
  θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p)

/-- The value `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`.  (The coefficient `_a₆` is unused, but
kept in the signature so `fval` and `fderiv` share the same interface.) -/
def fderiv (b₂ b₄ _b₆ : ℤ) (q : ℕ) (θ : ZMod q) : ZMod q :=
  3 * θ ^ 2 + 2 * (b₂ : ZMod q) * θ + (b₄ : ZMod q)

/-- The descent character as a raw function.  See the module docstring for the definition. -/
noncomputable def lambda (θ : ZMod p) : (curve a₂ a₄ a₆).toAffine.Point → ZMod 2
  | .zero => 0
  | .some x _ _ =>
      if (x.den : ZMod p) = 0 then 0
      else
        let α : ZMod p := (x.num : ZMod p) - θ * (x.den : ZMod p)
        if α = 0 then psi p (fderiv a₂ a₄ a₆ p θ) else psi p α

@[simp]
theorem lambda_zero (θ : ZMod p) :
    lambda a₂ a₄ a₆ p θ (0 : (curve a₂ a₄ a₆).toAffine.Point) = 0 :=
  rfl

/-! ### The hypotheses of the descent lemma

We package the arithmetic hypotheses as a structure so downstream tickets can pass them
around uniformly.  `p ∤ 6Δ` is expressed as: `p` prime, `p ∤ 6` (so `p ≠ 2, 3`), and the
integer discriminant is a unit mod `p`.  Since the coefficients are integers, `Δ` is an
integer, so `(curve …).Δ.num` is that integer and `(curve …).Δ.den = 1`. -/

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

end ECCompute
