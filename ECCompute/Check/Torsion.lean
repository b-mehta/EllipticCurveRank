/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import ECCompute.Check.F2Invert
import ECCompute.Theory.ModelIso

/-!
# Certifying the rational 2-torsion dimension `t = dim_𝔽₂ E(ℚ)[2]`

For a Weierstrass curve `W` over `ℚ`, a nonzero rational 2-torsion point `P` (`P + P = 0`, `P ≠ 0`)
is an affine point `(x, y)` with `P = -P`, i.e. `y = W.negY x y`. Its `x`-coordinate is a rational
root of the 2-division cubic `4x³ + b₂x² + 2b₄x + b₆`. Scaling by `u = 4x` turns this into the
**monic** integer cubic

  `g(u) = u³ + b₂ u² + 8 b₄ u + 16 b₆`,

so `u` is a rational root of a monic integer polynomial, hence an **integer** (integral root
theorem). Therefore, if `g` has no root modulo some prime `ℓ`, it has no integer root, so `W` has
no nonzero rational 2-torsion and `dim_𝔽₂ E(ℚ)[2] = 0`.

## Main definitions and results

* `ECCompute.hasRootMod c₂ c₁ c₀ ℓ` : a kernel-reducible `Bool`, `true` iff the monic cubic
  `u³ + c₂u² + c₁u + c₀` has a root modulo `ℓ` (checked over residues `0, …, ℓ-1`). No
  `native_decide`.
* `ECCompute.no_nonzero_twoTorsion_of_hasRootMod_eq_false` : the **t = 0 lemma** — if
  `hasRootMod W.b₂ (8 * W.b₄) (16 * W.b₆) ℓ = false`, then every 2-torsion point of `W` is `0`.

The correspondence used is elementary (`linear_combination`) rather than routed through mathlib's
`twoTorsionPolynomial`, whose root statement lives over a splitting field.
-/

namespace ECCompute

open WeierstrassCurve

/-- The value of the monic cubic `u³ + c₂u² + c₁u + c₀` at an integer `u`. -/
def cubicEval (c₂ c₁ c₀ u : ℤ) : ℤ := u ^ 3 + c₂ * u ^ 2 + c₁ * u + c₀

/-- Kernel-reducible test: `true` iff the monic integer cubic `u³ + c₂u² + c₁u + c₀` has a root
modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1`. This uses only `Int`/`Nat` arithmetic
and `%`, so it reduces by `decide`/`rfl` in the kernel without `native_decide`.

At a witness prime `ℓ`, `hasRootMod … ℓ = false` certifies that the cubic has no integer root,
hence (after the `u = 4x` scaling) that the 2-division cubic has no rational root. -/
noncomputable def hasRootMod (c₂ c₁ c₀ : ℤ) (ℓ : ℕ) : Bool :=
  anyBelow ℓ fun r => cubicEval c₂ c₁ c₀ (r : ℤ) % (ℓ : ℤ) == 0

/-- `cubicEval` is invariant, modulo `ℓ`, under changing its argument by a multiple of `ℓ`. -/
theorem cubicEval_modEq {c₂ c₁ c₀ : ℤ} (n : ℤ) {a b : ℤ} (h : a ≡ b [ZMOD n]) :
    cubicEval c₂ c₁ c₀ a ≡ cubicEval c₂ c₁ c₀ b [ZMOD n] := by
  unfold cubicEval
  exact ((h.pow 3).add ((Int.ModEq.refl c₂).mul (h.pow 2))).add
    ((Int.ModEq.refl c₁).mul h) |>.add (Int.ModEq.refl c₀)

/-- If the monic cubic has no root mod `ℓ` (with `ℓ ≠ 0`), it has no integer root. -/
theorem no_int_root_of_hasRootMod_eq_false {c₂ c₁ c₀ : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : hasRootMod c₂ c₁ c₀ ℓ = false) (u : ℤ) : cubicEval c₂ c₁ c₀ u ≠ 0 := by
  intro hu
  -- reduce `u` to its residue `r = u % ℓ ∈ {0, …, ℓ-1}`
  set r : ℤ := u % (ℓ : ℤ) with hr
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  have hr0 : 0 ≤ r := Int.emod_nonneg u (by exact_mod_cast hℓ)
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  -- `r.toNat` is congruent to `u` mod `ℓ`, and `cubicEval` at `u` is `0`, so the residue is a root
  have hcong : cubicEval c₂ c₁ c₀ (r.toNat : ℤ) % (ℓ : ℤ) = 0 := by
    have huv : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    have hmod : (r.toNat : ℤ) ≡ u [ZMOD (ℓ : ℤ)] := by
      rw [huv, hr]; exact Int.mod_modEq u _
    have hthis : cubicEval c₂ c₁ c₀ (r.toNat : ℤ) % (ℓ : ℤ) = cubicEval c₂ c₁ c₀ u % (ℓ : ℤ) :=
      cubicEval_modEq (ℓ : ℤ) hmod
    rw [hthis, hu, Int.zero_emod]
  -- but `hasRootMod = false` says no tested residue is a root — contradiction
  rw [hasRootMod, anyBelow_eq_false] at h
  have := h r.toNat (by omega)
  rw [beq_eq_false_iff_ne] at this
  exact this hcong

/-! ## The t = 0 lemma -/

open Polynomial in
/-- **t = 0 lemma.** Let `W` be the Weierstrass curve over `ℚ` with integer coefficients
`a₁ a₂ a₃ a₄ a₆`, and let `ℓ ≠ 0`. If the monic 2-division cubic
`u³ + b₂ u² + 8 b₄ u + 16 b₆` has no root modulo `ℓ`, then `W` has no nonzero rational 2-torsion:
every point `P` with `P + P = 0` is `0`.

A nonzero 2-torsion point `some x y` forces `y = W.negY x y`, so `u = 4x` is a rational root of the
monic integer cubic above; the integral root theorem makes `u` an integer, contradicting the
hypothesis via `no_int_root_of_hasRootMod_eq_false`. -/
theorem no_nonzero_twoTorsion_of_hasRootMod_eq_false
    (a₁ a₂ a₃ a₄ a₆ : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (W : WeierstrassCurve ℚ)
    (ha₁ : W.a₁ = a₁) (ha₂ : W.a₂ = a₂) (ha₃ : W.a₃ = a₃) (ha₄ : W.a₄ = a₄) (ha₆ : W.a₆ = a₆)
    (h : hasRootMod (a₁ ^ 2 + 4 * a₂) (8 * (2 * a₄ + a₁ * a₃)) (16 * (a₃ ^ 2 + 4 * a₆)) ℓ = false)
    (P : W.toAffine.Point) (hP : P + P = 0) : P = 0 := by
  -- eliminate the point-at-infinity case; work with `P = some x y h`
  obtain _ | ⟨x, y, hns⟩ := P
  · rfl
  exfalso
  -- `some x y + some x y = 0` forces `y = W.negY x y`
  have hy : y = W.toAffine.negY x y := by
    by_contra hne
    exact Affine.Point.some_ne_zero _ (by rw [Affine.Point.add_self_of_Y_ne hne] at hP; exact hP)
  -- the Weierstrass equation and the 2-torsion condition
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp hns.1
  have htor : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have := hy; simp only [WeierstrassCurve.Affine.negY] at this; linarith [this]
  -- `r = 4x` is a rational root of the monic integer cubic `⟨1, b₂, 8b₄, 16b₆⟩`
  set c₂ : ℤ := a₁ ^ 2 + 4 * a₂ with hc₂
  set c₁ : ℤ := 8 * (2 * a₄ + a₁ * a₃) with hc₁
  set c₀ : ℤ := 16 * (a₃ ^ 2 + 4 * a₆) with hc₀
  set p : ℤ[X] := Cubic.toPoly ⟨1, c₂, c₁, c₀⟩ with hp
  have hmonic : p.Monic := Cubic.monic_of_a_eq_one' ..
  -- evaluate the abstract cubic polynomial, keeping the integer coefficients opaque
  have haeval : aeval (4 * x : ℚ) p =
      (4 * x) ^ 3 + (c₂ : ℚ) * (4 * x) ^ 2 + (c₁ : ℚ) * (4 * x) + (c₀ : ℚ) := by
    simp only [hp, Cubic.toPoly, map_add, map_mul, map_pow, aeval_X, map_intCast,
      eq_intCast, Int.cast_one, one_mul]
  have hroot : aeval (4 * x : ℚ) p = 0 := by
    rw [haeval, hc₂, hc₁, hc₀]
    push_cast
    rw [← ha₁, ← ha₂, ← ha₃, ← ha₄, ← ha₆]
    linear_combination (-64 : ℚ) * heq + 16 * (W.a₁ * x + W.a₃ + 2 * y) * htor
  -- the integral root theorem: `4x` equals some integer `z`
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  -- `cubicEval c₂ c₁ c₀ z = 0` over ℤ, contradicting the no-root-mod hypothesis
  refine no_int_root_of_hasRootMod_eq_false hℓ h z ?_
  have hzcast : (4 * x : ℚ) = (z : ℚ) := by rw [hz]; simp
  -- cast the ℤ cubic value to ℚ and use the identity at `4x = z`
  have hQ : ((cubicEval c₂ c₁ c₀ z : ℤ) : ℚ) = 0 := by
    simp only [cubicEval, hc₂, hc₁, hc₀]
    push_cast
    rw [← hzcast, ← ha₁, ← ha₂, ← ha₃, ← ha₄, ← ha₆]
    linear_combination (-64 : ℚ) * heq + 16 * (W.a₁ * x + W.a₃ + 2 * y) * htor
  exact_mod_cast hQ

/-! ## Worked example: a `t = 0` certificate

We exhibit the `t = 0` certificate on a concrete integral Weierstrass model whose 2-division cubic
has no root modulo the witness prime `ℓ = 29`. (The rank-23 running curve of the project uses the
same `ℓ = 29`; its integer coefficients are not stored in this repository, so we use a stand-in
curve with the identical certificate shape here.)

For `a₁ = 1, a₂ = -3, a₃ = 1, a₄ = -3, a₆ = -2`, the monic 2-division cubic is
`u³ - 11 u² - 40 u - 112`, and the kernel-reducible check confirms it has no root mod `29`. -/

/-- The kernel check: the monic 2-division cubic of the example curve has no root mod `29`. -/
example : hasRootMod (-11) (-40) (-112) 29 = false := rfl

open ModelIso in
/-- Assembled `t = 0`: the example curve has no nonzero rational 2-torsion. -/
example (P : (toCurveQ 1 (-3) 1 (-3) (-2)).toAffine.Point) (hP : P + P = 0) : P = 0 :=
  no_nonzero_twoTorsion_of_hasRootMod_eq_false 1 (-3) 1 (-3) (-2) (ℓ := 29) (by norm_num)
    (toCurveQ 1 (-3) 1 (-3) (-2)) rfl rfl rfl rfl rfl rfl P hP

end ECCompute
