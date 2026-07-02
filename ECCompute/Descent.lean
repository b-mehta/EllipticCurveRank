import Mathlib

/-!
# The descent character (T1)

For an elliptic curve `E : y² = f(x)` with `f = x³ + a₂x² + a₄x + a₆` a monic integral
cubic of non-zero discriminant, a prime `p ∤ 6Δ`, and a root `θ ∈ 𝔽ₚ` of `f`, this file
defines the *descent character*

  `λ_{p,θ} : E(ℚ) → ZMod 2`

and states that it is an additive group homomorphism.  Being a homomorphism into `ZMod 2`
it automatically vanishes on `2·E(ℚ)`, hence factors through `E(ℚ)/2E(ℚ)`.

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
* `ECCompute.lambda_map_add` — **the trusted theorem**: `λ` is additive.  Proof `sorry`.
* `ECCompute.lambdaHom`  — `λ` packaged as an `AddMonoidHom`.
* `ECCompute.lambdaHom_two_nsmul` — `λ` vanishes on `2·E(ℚ)` (follows for free from `ZMod 2`).
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

/-! ### The trusted theorem: additivity

This is the sole mathematical obligation of ticket T1.  Everything else (the
`AddMonoidHom` packaging and vanishing on `2E`) is formal once this is proved. -/

/-- **Descent character is additive.**  Under the hypotheses `p ∤ 6Δ` and `f(θ) ≡ 0`, the
descent character `λ_{p,θ}` is a homomorphism `(E(ℚ), +) → (ZMod 2, +)`.  This is the one
trusted mathematical input of the whole development; see the proof plan below. -/
theorem lambda_map_add {θ : ZMod p} (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curve a₂ a₄ a₆).toAffine.Point) :
    lambda a₂ a₄ a₆ p θ (P + Q) = lambda a₂ a₄ a₆ p θ P + lambda a₂ a₄ a₆ p θ Q := by
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

/-!
## Proof plan for `lambda_map_add`  (the remaining `sorry`)

The additivity is a valuation / quadratic-residue computation.  Strategy:

**1. Reduce to the arithmetic of `α(P) := x(P).num − θ·x(P).den` in `𝔽ₚ`.**
   First establish the *denominator-is-a-square* lemma: for `P = (x,y)` on `E`, `x.den` is
   a perfect square in `ℕ` and, writing `x = u/w²` with `gcd(u,w)=1`, `x.num = u`,
   `x.den = w²`.  (Standard: clear denominators in `y² = f(x)`, use `f` integral monic.)
   Consequence used repeatedly: `(x.den : ZMod p)` is always a square, so
   `ψ_p(x.num − θ x.den) = ψ_p((x − θ)·w²)` is unchanged by the `w²` factor.

**2. Set up the local invariant.**  Define `μ(P) ∈ 𝔽ₚ* / (𝔽ₚ*)²` = "the class of `x(P) − θ`",
   with the two exceptional patches:
   * `P = O` and `p ∣ w` (bad reduction / point reducing to `O` mod `p`) ↦ trivial class;
   * `x(P) ≡ θ` (tangent case) ↦ class of `f'(θ)`.
   `λ = ψ_p ∘ μ` where `ψ_p` is the group iso `𝔽ₚ*/(𝔽ₚ*)² ≅ ZMod 2`.  So it suffices to
   show `μ` is a homomorphism `E(ℚ) → 𝔽ₚ*/(𝔽ₚ*)²`.

**3. Homomorphism property via the group law.**  For `P₁ + P₂ + P₃ = O` (collinear points
   on `E`, `y = ℓx + m`), one shows
     `(x₁ − θ)(x₂ − θ)(x₃ − θ) = (ℓθ + m − y(θ))²`  ... i.e. a *square* in `𝔽ₚ`,
   because `x³ + a₂x² + a₄x + a₆ − (ℓx+m)² = (x−x₁)(x−x₂)(x−x₃)` (the cubic minus the line²
   has those three roots), evaluated at `x = θ` and using `f(θ) = 0` so
   `f(θ) − (ℓθ+m)² = −(ℓθ+m)²`.  Hence `μ(P₁)μ(P₂)μ(P₃) = 1` in `𝔽ₚ*/(𝔽ₚ*)²`, and with
   `μ(−P) = μ(P)` (negation fixes `x`) this gives `μ(P₁+P₂) = μ(P₁)μ(P₂)`.  Push through
   `ψ_p` (a group hom to `ZMod 2`) to get additivity of `λ`.

**4. Exceptional cases.**
   * A factor `xᵢ − θ` vanishes mod `p` ⇔ that point reduces to the `θ`-2-torsion point mod
     `p`.  There `f'(θ) ≠ 0` (simple root, from `p ∤ 6Δ`) replaces `xᵢ − θ`; the identity of
     step 3 degenerates to the tangent/`f'(θ)` value — this is exactly the `α = 0` branch.
   * `p ∣ w` (a `Pᵢ` reduces to `O` mod `p`): that factor contributes a square (the reduction
     is `O`, contributing trivially), matching the `λ = 0` clause.
   Formally: work in `ℚ_p` (or with `p`-adic valuations `Int → WithTop ℕ`) so that "reduces
   to" statements are clean; `p ∤ 6Δ` guarantees good reduction of `E` at `p` and simple
   roots of `f mod p`, so the reduction map `E(ℚ) → E(𝔽ₚ)` is a homomorphism compatible with
   `x ↦ x − θ`.

**5. Vanishing on `2E` is free** (already proved): `λ` into `ZMod 2` and `x + x = 0` there.
   So `λ(2P) = 2·λ(P) = 0`; no separate valuation argument is needed for this half of the
   ticket statement.

Mathlib inputs to lean on: `WeierstrassCurve.Affine.Point.add_of_X_ne` / `add_some` and the
slope formulae (`WeierstrassCurve.Affine.slope`, `addX`, `addY`) for the collinearity
identity; `Cubic`/`Polynomial.roots` for the "cubic − line² factors as `∏(x−xᵢ)`" step;
`ZMod.isSquare_*` / `legendreSym` / `ZMod.unitsMap` and the isomorphism
`𝔽ₚ*/(𝔽ₚ*)² ≅ ZMod 2` for `ψ_p` being a homomorphism; `Rat.num`, `Rat.den`, and
`WeierstrassCurve` reduction (`WeierstrassCurve.map`) for the arithmetic in steps 1 & 4.
-/
