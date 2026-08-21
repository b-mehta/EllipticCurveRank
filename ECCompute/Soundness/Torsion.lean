/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness.RootMod
import ECCompute.Theory.Descent.Defs

/-!
# Certifying the rational 2-torsion dimension `t = dim_𝔽₂ E(ℚ)[2]`

For a Weierstrass curve `W` over `ℚ`, the `x`-coordinate of a nonzero rational 2-torsion point
scales (`u = 4x`) to an integer root of the monic cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆`. So if this
cubic has no root modulo some prime `ℓ` (via `ECCompute.monicHasNoRootMod`),
then `W` has no nonzero rational 2-torsion and `dim_𝔽₂ E(ℚ)[2] = 0`.

## Main results

* `ECCompute.no_nonzero_twoTorsion_of_monicHasNoRootMod` : the t = 0 lemma. If the `2`-division
  cubic's search returns `true` (no root), then every 2-torsion point of `W` is `0`.
* `ECCompute.card_twoTorsion_le_four`, `ECCompute.card_twoTorsion_le_two_of_root_cofactor`,
  `ECCompute.certTorsionBound_zero/one/two` : the counting bounds behind each torsion mode.
-/

namespace ECCompute

open WeierstrassCurve

/-! ## The t = 0 lemma -/

open Polynomial in
/-- If `some x y` is nonzero 2-torsion on `W` (via the Weierstrass and 2-torsion equations), then
`4x` is an integer root of the monic 2-division cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆`. -/
private theorem exists_intRoot_of_twoTorsion (a₁ a₂ a₃ a₄ a₆ : ℤ) (W : WeierstrassCurve ℚ)
    (ha₁ : W.a₁ = a₁) (ha₂ : W.a₂ = a₂) (ha₃ : W.a₃ = a₃) (ha₄ : W.a₄ = a₄) (ha₆ : W.a₆ = a₆)
    {x y : ℚ}
    (heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (htor : 2 * y + W.a₁ * x + W.a₃ = 0) :
    ∃ z : ℤ,
      polyEval [16 * (a₃ ^ 2 + 4 * a₆), 8 * (2 * a₄ + a₁ * a₃), a₁ ^ 2 + 4 * a₂, 1] z = 0 := by
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
    grind
  -- the integral root theorem: `4x` equals some integer `z`
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  have hzcast : (4 * x : ℚ) = (z : ℚ) := by simp [hz]
  refine ⟨z, ?_⟩
  -- cast the ℤ cubic value to ℚ and use the identity at `4x = z`
  have hQ : ((polyEval [c₀, c₁, c₂, 1] z : ℤ) : ℚ) = 0 := by
    simp only [polyEval, Int.add_def, Int.mul_def, hc₂, hc₁, hc₀]
    push_cast
    grind
  exact_mod_cast hQ

/-- Let `W` be the Weierstrass curve over `ℚ` with integer coefficients `a₁ a₂ a₃ a₄ a₆`, and let
`1 < ℓ`. If the monic 2-division cubic `u³ + b₂ u² + 8 b₄ u + 16 b₆` has no root modulo `ℓ`, then
`W` has no nonzero rational 2-torsion: every point `P` with `P + P = 0` is `0`. -/
theorem no_nonzero_twoTorsion_of_monicHasNoRootMod
    (a₁ a₂ a₃ a₄ a₆ : ℤ) {ℓ : ℕ} (hℓ : 1 < ℓ)
    (W : WeierstrassCurve ℚ)
    (ha₁ : W.a₁ = a₁) (ha₂ : W.a₂ = a₂) (ha₃ : W.a₃ = a₃) (ha₄ : W.a₄ = a₄) (ha₆ : W.a₆ = a₆)
    (h : monicHasNoRootMod
      [16 * (a₃ ^ 2 + 4 * a₆), 8 * (2 * a₄ + a₁ * a₃), a₁ ^ 2 + 4 * a₂] ℓ = true)
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
    grind [WeierstrassCurve.Affine.negY]
  -- `4x` is an integer root of the cubic, contradicting the no-root-mod hypothesis
  obtain ⟨z, hz⟩ :=
    exists_intRoot_of_twoTorsion a₁ a₂ a₃ a₄ a₆ W ha₁ ha₂ ha₃ ha₄ ha₆ heq htor
  exact no_int_root_of_monicHasNoRootMod hℓ h z hz

/-! ## The universal bound `|E(ℚ)[2]| ≤ 4`

For the short model `curve a₂ a₄ a₆` (with `a₁ = a₃ = 0`), a nonzero rational `2`-torsion point is
`(x, 0)` where `x` is a rational root of `f = X³ + a₂X² + a₄X + a₆`. Since `f` has at most three
roots, the full `2`-torsion has at most four elements. This is the torsion witness for
certificates with `t = 2` (full rational `2`-torsion, e.g. curves with square discriminant),
for which the bound `rank ≥ ρ - t` needs only `|E(ℚ)[2]| ≤ 2^t = 4`. -/

open Polynomial in
/-- On the short model, a nonzero rational `2`-torsion point `some x y` has `y = 0`, and its
`x`-coordinate is a root of the cubic `X³ + a₂X² + a₄X + a₆`. -/
private theorem twoTorsion_y_eq_zero_and_root (a₂ a₄ a₆ : ℤ) {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Affine.Point.some x y h + Affine.Point.some x y h = 0) :
    y = 0 ∧ x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots := by
  have hmonic : (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).toPoly.Monic :=
    Cubic.monic_of_a_eq_one' ..
  have hy : y = (curve a₂ a₄ a₆).toAffine.negY x y := by
    by_contra hne
    exact Affine.Point.some_ne_zero _
      (by rw [Affine.Point.add_self_of_Y_ne hne] at hP; exact hP)
  have hy0 : y = 0 := by
    grind [WeierstrassCurve.Affine.negY, curve]
  refine ⟨hy0, ?_⟩
  rw [Cubic.mem_roots_iff hmonic.ne_zero]
  have heq := (WeierstrassCurve.Affine.equation_iff _ _).mp h.1
  simp only [curve] at heq
  rw [hy0] at heq
  grind

/-- Core counting step for every torsion bound: if the `x`-coordinates of all nonzero rational
`2`-torsion points lie in a finite set `Sx`, then the `2`-torsion set is finite with at most
`|Sx| + 1` elements (the identity plus one point `(x, 0)` per allowed `x`). Each concrete bound
just supplies an `Sx`: the cubic's roots (`≤ 3`) for the universal case, a singleton for `t = 1`. -/
private theorem card_twoTorsion_le_of_xcoords (a₂ a₄ a₆ : ℤ) (Sx : Finset ℚ)
    (hx : ∀ (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y),
        Affine.Point.some x y h + Affine.Point.some x y h = 0 → x ∈ Sx) :
    ({P | P + P = 0} : Set (curve a₂ a₄ a₆).toAffine.Point).Finite ∧
      Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ Sx.card + 1 := by
  classical
  set W := curve a₂ a₄ a₆ with hW
  set T : Set W.toAffine.Point := {P | P + P = 0} with hT
  set ι : W.toAffine.Point → Option ℚ :=
    fun P ↦ match P with
      | .zero => none
      | .some x _ _ => some x with hιdef
  set S : Finset (Option ℚ) := Sx.insertNone with hS
  have hinj : Set.InjOn ι T := by
    intro P hP P' hP' hEq
    simp only [hT, Set.mem_ofPred_eq] at hP hP'
    obtain _ | ⟨x, y, h⟩ := P
    · obtain _ | ⟨x', y', h'⟩ := P'
      · rfl
      · simp [hιdef] at hEq
    · obtain _ | ⟨x', y', h'⟩ := P'
      · simp [hιdef] at hEq
      · simp only [hιdef, Option.some.injEq] at hEq
        subst hEq
        obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root a₂ a₄ a₆ h hP
        obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root a₂ a₄ a₆ h' hP'
        rfl
  have himg : ι '' T ⊆ ↑S := by
    rintro o ⟨P, hP, rfl⟩
    simp only [hT, Set.mem_ofPred_eq] at hP
    obtain _ | ⟨x, y, h⟩ := P
    · simp [hιdef, hS]
    · simp only [hιdef, hS, Finset.mem_coe, Finset.some_mem_insertNone]
      exact hx x y h hP
  refine ⟨Set.Finite.of_finite_image (S.finite_toSet.subset himg) hinj, ?_⟩
  have hcard : Nat.card {P : W.toAffine.Point // P + P = 0} = T.ncard :=
    (Nat.card_coe_set_eq T).symm
  rw [hcard]
  calc T.ncard
      = (ι '' T).ncard := (hinj.ncard_image).symm
    _ ≤ (↑S : Set (Option ℚ)).ncard := Set.ncard_le_ncard himg S.finite_toSet
    _ = S.card := Set.ncard_coe_finset S
    _ = Sx.card + 1 := Finset.card_insertNone Sx

open Polynomial in
/-- Every nonzero rational `2`-torsion `x`-coordinate is a root of the `2`-division cubic. -/
private theorem twoTorsion_xcoord_mem_roots (a₂ a₄ a₆ : ℤ) (x y : ℚ)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Affine.Point.some x y h + Affine.Point.some x y h = 0) :
    x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots.toFinset :=
  Multiset.mem_toFinset.mpr (twoTorsion_y_eq_zero_and_root a₂ a₄ a₆ h hP).2

/-- The `2`-torsion set of the short model `curve a₂ a₄ a₆` is finite. -/
instance twoTorsion_finite (a₂ a₄ a₆ : ℤ) :
    Finite {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} :=
  (card_twoTorsion_le_of_xcoords a₂ a₄ a₆ _ (twoTorsion_xcoord_mem_roots a₂ a₄ a₆)).1.to_subtype

open Polynomial in
/-- The rational `2`-torsion of the short model `curve a₂ a₄ a₆` has at most four elements: the
identity together with the (at most three) nonzero points `(x, 0)` for `x` a root of the cubic. -/
theorem card_twoTorsion_le_four (a₂ a₄ a₆ : ℤ) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 4 := by
  have h := (card_twoTorsion_le_of_xcoords a₂ a₄ a₆ _ (twoTorsion_xcoord_mem_roots a₂ a₄ a₆)).2
  have := Cubic.card_roots_le (P := (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ))
  lia

/-- The `t = 0` witness: if the monic `2`-division cubic of the short model has no root modulo a
witness prime `ℓ` (`1 < ℓ`), then the only rational `2`-torsion point is the identity, so the
`2`-torsion has at most one element. -/
theorem card_twoTorsion_le_one_of_monicHasNoRootMod (a₂ a₄ a₆ : ℤ) {ℓ : ℕ} (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ = true) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 1 := by
  have hnn : ∀ P : (curve a₂ a₄ a₆).toAffine.Point, P + P = 0 → P = 0 := by
    intro P hP
    refine no_nonzero_twoTorsion_of_monicHasNoRootMod 0 a₂ 0 a₄ a₆ hℓ _
      rfl rfl rfl rfl rfl ?_ P hP
    have e1 : (0 : ℤ) ^ 2 + 4 * a₂ = 4 * a₂ := by ring
    have e2 : 8 * (2 * a₄ + 0 * 0) = 16 * a₄ := by ring
    have e3 : 16 * ((0 : ℤ) ^ 2 + 4 * a₆) = 64 * a₆ := by ring
    rw [e1, e2, e3]
    exact h
  have : Subsingleton {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} :=
    ⟨fun a b ↦ Subtype.ext (by rw [hnn a.1 a.2, hnn b.1 b.2])⟩
  exact Finite.card_le_one_iff_subsingleton.mpr this

/-! ## The `t = 1` bound `|E(ℚ)[2]| ≤ 2`

If the `2`-division cubic `F = X³ + a₂X² + a₄X + a₆` has an integer root `R`, then it factors as
`F = (X - R) · q` with `q = X² + (a₂ + R)X + (a₄ + R(a₂ + R))`. If `q` has no rational root (again
certified by a prime `ℓ` modulo which `q` has no root), then `R` is the *only* rational root of `F`,
so the nonzero `2`-torsion points all share the `x`-coordinate `R`, giving `|E(ℚ)[2]| ≤ 2`. -/

/-- Over `ℚ`, the `2`-division cubic factors as `F = (X - R) · q` at an integer root `R`: an
identity in the coefficients, valid whenever `polyEval [a₆, a₄, a₂, 1] R = 0`. -/
private theorem cubic_factor_at_root (a₂ a₄ a₆ R : ℤ) (hR : polyEval [a₆, a₄, a₂, 1] R = 0)
    (x : ℚ) :
    x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ)
      = (x - R) * (x ^ 2 + ((a₂ : ℚ) + R) * x + ((a₄ : ℚ) + R * ((a₂ : ℚ) + R))) := by
  have hRQ : (R : ℚ) ^ 3 + (a₂ : ℚ) * R ^ 2 + (a₄ : ℚ) * R + (a₆ : ℚ) = 0 := by
    have hz : ((polyEval [a₆, a₄, a₂, 1] R : ℤ) : ℚ) = 0 := by simp [hR]
    simp only [polyEval, Int.add_def, Int.mul_def] at hz
    push_cast at hz
    linear_combination hz
  grind

/-- If the `2`-division cubic `F` of the short model has integer root `R` and its cofactor quadratic
`q = X² + (a₂+R)X + (a₄+R(a₂+R))` has no rational root (witnessed by `1 < ℓ`), then every rational
root of `F` equals `R`. -/
private theorem root_eq_of_cofactor_no_root (a₂ a₄ a₆ R : ℤ) (hR : polyEval [a₆, a₄, a₂, 1] R = 0)
    {ℓ : ℕ} (hℓ : 1 < ℓ)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ = true)
    {x : ℚ} (hx : x ^ 3 + (a₂ : ℚ) * x ^ 2 + (a₄ : ℚ) * x + (a₆ : ℚ) = 0) :
    x = (R : ℚ) := by
  rw [cubic_factor_at_root a₂ a₄ a₆ R hR, mul_eq_zero] at hx
  rcases hx with h | h
  · grind
  · refine absurd h fun hqx ↦
      no_rat_root_of_monicHasNoRootMod hℓ hq x ?_
    grind

open Polynomial in
/-- The `t = 1` bound. If the short model's `2`-division cubic has an integer root `R` and its
cofactor quadratic has no rational root (via a prime `ℓ` (`1 < ℓ`)), then every nonzero rational
`2`-torsion point has `x`-coordinate `R`, so the `2`-torsion has at most two elements. -/
theorem card_twoTorsion_le_two_of_root_cofactor (a₂ a₄ a₆ R : ℤ)
    (hR : polyEval [a₆, a₄, a₂, 1] R = 0) {ℓ : ℕ} (hℓ : 1 < ℓ)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ = true) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 2 := by
  -- every nonzero `2`-torsion `x`-coordinate is a root of the cubic, hence equal to `R`
  have hx : ∀ (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y),
      Affine.Point.some x y h + Affine.Point.some x y h = 0 → x ∈ ({(R : ℚ)} : Finset ℚ) := by
    intro x y h hP
    obtain ⟨-, hroot⟩ := twoTorsion_y_eq_zero_and_root a₂ a₄ a₆ h hP
    rw [Cubic.mem_roots_iff (Cubic.monic_of_a_eq_one' ..).ne_zero] at hroot
    refine Finset.mem_singleton.mpr (root_eq_of_cofactor_no_root a₂ a₄ a₆ R hR hℓ hq ?_)
    grind
  have h := (card_twoTorsion_le_of_xcoords a₂ a₄ a₆ _ hx).2
  simpa using h

/-! ## Certificate-facing torsion bounds

These three wrappers take kernel-`Bool` witnesses (dischargeable by `reflBoolTrue`) and produce the
`|E(ℚ)[2]| ≤ 2^t` bound the certificate soundness theorem consumes: `t = 0` from a no-root witness,
`t = 1` from an integer root whose cofactor has no root mod `ℓ`, and `t = 2` unconditionally (the
universal `≤ 4` bound). -/

/-- The `t = 0` certificate torsion bound from `Bool` witnesses. -/
theorem certTorsionBound_zero (a₂ a₄ a₆ : ℤ) (ℓ : ℕ) (hp : Nat.blt 1 ℓ = true)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ = true) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 2 ^ 0 := by
  rw [pow_zero]
  exact card_twoTorsion_le_one_of_monicHasNoRootMod a₂ a₄ a₆
    (by simpa using hp) h

/-- The `t = 1` certificate torsion bound from `Bool` witnesses: an integer root `R` of the
`2`-division cubic (`polyEval [a₆, a₄, a₂, 1] R == 0`) whose cofactor quadratic has no root modulo
a prime `ℓ` (`1 < ℓ`). Yields `|E(ℚ)[2]| ≤ 2 = 2^1`. -/
theorem certTorsionBound_one (a₂ a₄ a₆ R : ℤ) (ℓ : ℕ) (hp : Nat.blt 1 ℓ = true)
    (hR : (polyEval [a₆, a₄, a₂, 1] R).beq' 0 = true)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ = true) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 2 ^ 1 := by
  rw [pow_one]
  exact card_twoTorsion_le_two_of_root_cofactor a₂ a₄ a₆ R
    (by simpa [Int.beq'_eq] using hR)
    (by simpa using hp) hq

/-- The `t = 2` certificate torsion bound: the universal `|E(ℚ)[2]| ≤ 4 = 2^2`. -/
theorem certTorsionBound_two (a₂ a₄ a₆ : ℤ) :
    Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} ≤ 2 ^ 2 :=
  card_twoTorsion_le_four a₂ a₄ a₆

end ECCompute
