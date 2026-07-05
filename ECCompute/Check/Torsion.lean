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

For a Weierstrass curve `W` over `ℚ`, the `x`-coordinate of a nonzero rational 2-torsion point
scales (`u = 4x`) to an integer root of the monic cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆`. So if this
cubic has no root modulo some prime `ℓ`, then `W` has no nonzero rational 2-torsion and
`dim_𝔽₂ E(ℚ)[2] = 0`.

## Main definitions and results

* `ECCompute.hasRootMod c₂ c₁ c₀ ℓ` : a kernel-reducible `Bool`, `true` iff the monic cubic
  `u³ + c₂u² + c₁u + c₀` has a root modulo `ℓ` (checked over residues `0, …, ℓ-1`).
* `ECCompute.no_nonzero_twoTorsion_of_hasRootMod_eq_false` : the t = 0 lemma. If
  `hasRootMod W.b₂ (8 * W.b₄) (16 * W.b₆) ℓ = false`, then every 2-torsion point of `W` is `0`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The value of the monic cubic `u³ + c₂u² + c₁u + c₀` at an integer `u`. -/
def cubicEval (c₂ c₁ c₀ u : ℤ) : ℤ := u ^ 3 + c₂ * u ^ 2 + c₁ * u + c₀

/-- Kernel-reducible test: `true` iff the monic integer cubic `u³ + c₂u² + c₁u + c₀` has a root
modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1`. -/
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
    have hmod : (r.toNat : ℤ) ≡ u [ZMOD (ℓ : ℤ)] := by rw [huv, hr]; exact Int.mod_modEq u _
    have hthis : cubicEval c₂ c₁ c₀ (r.toNat : ℤ) % (ℓ : ℤ) = cubicEval c₂ c₁ c₀ u % (ℓ : ℤ) :=
      cubicEval_modEq (ℓ : ℤ) hmod
    rw [hthis, hu, Int.zero_emod]
  -- but `hasRootMod = false` says no tested residue is a root, a contradiction
  rw [hasRootMod, anyBelow_eq_false] at h
  grind

/-! ## The t = 0 lemma -/

/-- The scaled coordinate `4x` of a nonzero 2-torsion point is a root of the monic 2-division
cubic, written as an identity in the curve coefficients. -/
private theorem cubic_fourX_eq_zero (W : WeierstrassCurve ℚ) {x y : ℚ}
    (heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (htor : 2 * y + W.a₁ * x + W.a₃ = 0) :
    (4 * x) ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * (4 * x) ^ 2
      + 8 * (2 * W.a₄ + W.a₁ * W.a₃) * (4 * x) + 16 * (W.a₃ ^ 2 + 4 * W.a₆) = 0 := by
  linear_combination (-64 : ℚ) * heq + 16 * (W.a₁ * x + W.a₃ + 2 * y) * htor

open Polynomial in
/-- If `some x y` is nonzero 2-torsion on `W` (via the Weierstrass and 2-torsion equations), then
`4x` is an integer root of the monic 2-division cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆`. -/
private theorem exists_intRoot_of_twoTorsion (a₁ a₂ a₃ a₄ a₆ : ℤ) (W : WeierstrassCurve ℚ)
    (ha₁ : W.a₁ = a₁) (ha₂ : W.a₂ = a₂) (ha₃ : W.a₃ = a₃) (ha₄ : W.a₄ = a₄) (ha₆ : W.a₆ = a₆)
    {x y : ℚ}
    (heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (htor : 2 * y + W.a₁ * x + W.a₃ = 0) :
    ∃ z : ℤ,
      cubicEval (a₁ ^ 2 + 4 * a₂) (8 * (2 * a₄ + a₁ * a₃)) (16 * (a₃ ^ 2 + 4 * a₆)) z = 0 := by
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
    exact cubic_fourX_eq_zero W heq htor
  -- the integral root theorem: `4x` equals some integer `z`
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  have hzcast : (4 * x : ℚ) = (z : ℚ) := by rw [hz]; simp
  refine ⟨z, ?_⟩
  -- cast the ℤ cubic value to ℚ and use the identity at `4x = z`
  have hQ : ((cubicEval c₂ c₁ c₀ z : ℤ) : ℚ) = 0 := by
    simp only [cubicEval, hc₂, hc₁, hc₀]
    push_cast
    rw [← hzcast, ← ha₁, ← ha₂, ← ha₃, ← ha₄, ← ha₆]
    exact cubic_fourX_eq_zero W heq htor
  exact_mod_cast hQ

/-- Let `W` be the Weierstrass curve over `ℚ` with integer coefficients `a₁ a₂ a₃ a₄ a₆`, and let
`ℓ ≠ 0`. If the monic 2-division cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆` has no root modulo `ℓ`, then
`W` has no nonzero rational 2-torsion: every point `P` with `P + P = 0` is `0`. -/
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
  -- `4x` is an integer root of the cubic, contradicting the no-root-mod hypothesis
  obtain ⟨z, hz⟩ :=
    exists_intRoot_of_twoTorsion a₁ a₂ a₃ a₄ a₆ W ha₁ ha₂ ha₃ ha₄ ha₆ heq htor
  exact no_int_root_of_hasRootMod_eq_false hℓ h z hz

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
