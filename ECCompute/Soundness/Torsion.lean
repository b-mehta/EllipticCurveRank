/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.ForMathlib.TwoTorsion
public import ECCompute.Soundness.RootMod
public import ECCompute.Theory.Descent.Character

import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Certifying the rational 2-torsion dimension `t = dim_𝔽₂ E(ℚ)[2]`

On the short model `curve a₂ a₄ a₆` (`a₁ = a₃ = 0`), a nonzero rational `2`-torsion point is
`(x, 0)` with `x` a root of the `2`-division cubic `X³ + a₂X² + a₄X + a₆`. This file certifies the
bound `|E(ℚ)[2]| ≤ 2 ^ t` on the rational `2`-torsion dimension `t = dim_𝔽₂ E(ℚ)[2]`, for
`t = 0, 1, 2`, from kernel-`Bool` witnesses on the cubic.

## Main results

* `ECCompute.certTorsionBound_zero`, `ECCompute.certTorsionBound_one`,
  `ECCompute.certTorsionBound_two` : the `|E(ℚ)[2]| ≤ 2 ^ t` bound from kernel-`Bool` witnesses,
  for `t = 0, 1, 2`.
-/

namespace ECCompute

open WeierstrassCurve Affine Polynomial

variable {a₂ a₄ a₆ : ℤ}

/-! ## Shared setup

A nonzero rational `2`-torsion point of the short model has `y = 0` and `x`-coordinate a root of
the cubic; confining those `x`-coordinates to a finite set bounds the whole `2`-torsion. -/

/-- The monic cubic `X³ + b X² + c X + d`, evaluated at `r` by `polyEval` and cast to `ℚ`, equals
`r³ + b r² + c r + d`. -/
lemma polyEval_monicCubic_cast {b c d r : ℤ} :
    (polyEval [d, c, b, 1] r : ℚ) = r ^ 3 + b * r ^ 2 + c * r + d := by
  simp only [polyEval]
  grind

/-- On the short model, a nonzero rational `2`-torsion point `some x y` has `y = 0`, and its
`x`-coordinate is a root of the cubic `X³ + a₂X² + a₄X + a₆`. -/
theorem twoTorsion_y_eq_zero_and_root {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Point.some x y h ∈ (curve a₂ a₄ a₆).twoTorsionPoints) :
    y = 0 ∧ x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots := by
  have hmonic : (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).toPoly.Monic := Cubic.monic_of_a_eq_one' ..
  have hy : y = (curve a₂ a₄ a₆).toAffine.negY x y := Y_eq_negY_of_add_self (curve a₂ a₄ a₆) h hP
  have hy0 : y = 0 := by grind [negY, curve]
  refine ⟨hy0, ?_⟩
  rw [Cubic.mem_roots_iff hmonic.ne_zero]
  grind [equation_curve, h.1]

/-- Every nonzero rational `2`-torsion `x`-coordinate is a root of the `2`-division cubic. -/
theorem twoTorsion_xcoord_mem_roots (x y : ℚ)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Point.some x y h ∈ (curve a₂ a₄ a₆).twoTorsionPoints) :
    x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots.toFinset :=
  Multiset.mem_toFinset.mpr (twoTorsion_y_eq_zero_and_root h hP).2

/-- If the `x`-coordinates of all nonzero rational `2`-torsion points lie in a finite set `Sx`, then
the `2`-torsion set is finite with at most `|Sx| + 1` elements: the identity together with one point
`(x, 0)` for each allowed `x`. -/
theorem card_twoTorsion_le_of_xcoords {Sx : Finset ℚ}
    (hx : ∀ (x y : ℚ) (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y),
        Point.some x y h + Point.some x y h = 0 → x ∈ Sx) :
    (curve a₂ a₄ a₆).twoTorsionPoints.Finite ∧
      (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ Sx.card + 1 := by
  classical
  set W := curve a₂ a₄ a₆
  set T : Set W.toAffine.Point := W.twoTorsionPoints with hT
  set ι : W.toAffine.Point → Option ℚ := fun
    | .zero => none
    | .some x _ _ => some x with hιdef
  set S : Finset (Option ℚ) := Sx.insertNone with hS
  have hinj : Set.InjOn ι T := by
    intro P hP P' hP' hEq
    obtain _ | ⟨x, y, h⟩ := P
    · grind
    obtain _ | ⟨x', y', h'⟩ := P'
    · simp [hιdef] at hEq
    simp only [hιdef, Option.some.injEq] at hEq
    subst hEq
    obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root h hP
    obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root h' hP'
    rfl
  have himg : ι '' T ⊆ S := by
    rintro o ⟨P, hP, rfl⟩
    obtain _ | ⟨x, y, h⟩ := P
    · simp [hιdef, hS]
    · simp only [hιdef, hS, Finset.mem_coe, Finset.some_mem_insertNone]
      exact hx x y h hP
  refine ⟨Set.Finite.of_finite_image (S.finite_toSet.subset himg) hinj, ?_⟩
  calc T.ncard
      = (ι '' T).ncard := hinj.ncard_image.symm
    _ ≤ (S : Set (Option ℚ)).ncard := Set.ncard_le_ncard himg S.finite_toSet
    _ = S.card := Set.ncard_coe_finset S
    _ = Sx.card + 1 := Finset.card_insertNone Sx

/-- The `2`-torsion set of the short model `curve a₂ a₄ a₆` is finite. -/
public instance : Finite (curve a₂ a₄ a₆).twoTorsionPoints :=
  (card_twoTorsion_le_of_xcoords twoTorsion_xcoord_mem_roots).1.to_subtype

/-! ## The universal bound `t = 2` -/

variable {ℓ : ℕ} {R : ℤ}

/-! ## The `t = 0` bound -/

/-- The `t = 0` bound: if the scaled `2`-division cubic of the short model has no root modulo a
witness prime `ℓ` (`1 < ℓ`), then the only rational `2`-torsion point is the identity, so the
`2`-torsion has at most one element. -/
theorem card_twoTorsion_le_one_of_monicHasNoRootMod (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ) :
    (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 1 := by
  suffices ∀ (x y : ℚ) (hns : (curve a₂ a₄ a₆).toAffine.Nonsingular x y),
      Point.some x y hns + Point.some x y hns = 0 → x ∈ (∅ : Finset ℚ) by
    simpa using (card_twoTorsion_le_of_xcoords this).2
  intro x y hns hP
  obtain ⟨hy0, -⟩ := twoTorsion_y_eq_zero_and_root hns hP
  have hxr : x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ = 0 := by grind [equation_curve hns.1]
  -- `x` roots the monic integer cubic, so it is an integer
  set p : ℤ[X] := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆ with hp
  have hmonic : p.Monic := by simp only [hp]; monicity!
  have haeval : p.aeval x = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by simp [hp]
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic (haeval.trans hxr)
  simp only [algebraMap_int_eq, eq_intCast] at hz
  -- `4z = 4x` is an integer root of the scaled cubic, contradicting the no-root-mod witness
  refine (no_int_root_of_monicHasNoRootMod hℓ h (4 * z) ?_).elim
  have hQ : (polyEval [64 * a₆, 16 * a₄, 4 * a₂, 1] (4 * z) : ℚ) = 0 := by
    grind [polyEval_monicCubic_cast]
  exact mod_cast hQ

/-! ## The `t = 1` bound -/

/-- The `t = 1` bound. If the short model's `2`-division cubic has an integer root `R` and its
cofactor quadratic has no rational root (via a prime `ℓ` (`1 < ℓ`)), then every nonzero rational
`2`-torsion point has `x`-coordinate `R`, so the `2`-torsion has at most two elements. -/
theorem card_twoTorsion_le_two_of_root_cofactor
    (hR : polyEval [a₆, a₄, a₂, 1] R = 0) (hℓ : 1 < ℓ)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ) :
    (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 := by
  suffices ∀ (x y : ℚ) (hns : (curve a₂ a₄ a₆).toAffine.Nonsingular x y),
      Point.some x y hns + Point.some x y hns = 0 → x ∈ ({(R : ℚ)} : Finset ℚ) by
    simpa using (card_twoTorsion_le_of_xcoords this).2
  -- every nonzero `2`-torsion `x`-coordinate is a root of the cubic, hence equal to `R`
  intro x y hns hP
  obtain ⟨-, hroot⟩ := twoTorsion_y_eq_zero_and_root _ hP
  rw [Cubic.mem_roots_iff (Cubic.monic_of_a_eq_one' ..).ne_zero] at hroot
  have hRQ : (R : ℚ) ^ 3 + a₂ * R ^ 2 + a₄ * R + a₆ = 0 := by
    rw [← polyEval_monicCubic_cast]
    exact mod_cast hR
  grind [no_rat_root_of_monicHasNoRootMod]

/-! ## Certificate-facing torsion bounds

Three wrappers taking kernel-`Bool` witnesses and producing the `|E(ℚ)[2]| ≤ 2 ^ t` bound: `t = 0`
from a no-root witness, `t = 1` from an integer root whose cofactor has no root mod `ℓ`, `t = 2`
unconditionally. -/

/-- The `t = 0` certificate torsion bound from `Bool` witnesses. -/
public theorem certTorsionBound_zero (hp : Nat.blt 1 ℓ)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ) :
    (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 0 :=
  card_twoTorsion_le_one_of_monicHasNoRootMod (by simpa using hp) h

/-- The `t = 1` certificate torsion bound from `Bool` witnesses: an integer root `R` of the
`2`-division cubic (`polyEval [a₆, a₄, a₂, 1] R == 0`) whose cofactor quadratic has no root modulo
a prime `ℓ` (`1 < ℓ`). Yields `|E(ℚ)[2]| ≤ 2 = 2^1`. -/
public theorem certTorsionBound_one (hp : Nat.blt 1 ℓ)
    (hR : (polyEval [a₆, a₄, a₂, 1] R).beq' 0)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ) :
    (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 1 :=
  card_twoTorsion_le_two_of_root_cofactor (by simpa [Int.beq'_eq] using hR) (by simpa using hp) hq

/-- The `t = 2` certificate torsion bound: the universal `|E(ℚ)[2]| ≤ 4 = 2^2`, since the rational
`2`-torsion is the identity together with the (at most three) nonzero points `(x, 0)` for `x` a
root of the `2`-division cubic. -/
public theorem certTorsionBound_two : (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 2 := by
  change (curve a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 4
  grw [(card_twoTorsion_le_of_xcoords twoTorsion_xcoord_mem_roots).2, Cubic.card_roots_le]

end ECCompute
