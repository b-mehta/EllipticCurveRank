/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Soundness.Fold
public import Mathlib.Data.ZMod.Basic

import Mathlib.RingTheory.Polynomial.RationalRoot
import ECCompute.ForLean

/-!
# Soundness of the monic residue search

Correctness proofs for the kernel `Bool` checker `ECCompute.monicHasNoRootMod` (defined in
`ECCompute.Kernel`): for a monic integer polynomial given by a coefficient list `cs` and a modulus
`ℓ`, a passing residue search over `0, …, ℓ - 1` rules out an integer root, and for a monic
quadratic a rational one.

## Main results

* `ECCompute.no_int_root_of_monicHasNoRootMod`: a residue search finding no root rules out an
  integer root.
* `ECCompute.no_rat_root_of_monicHasNoRootMod`: for a monic quadratic, it rules out a rational
  root.
-/

namespace ECCompute

variable {cs : List ℤ} {ℓ r : ℕ}

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p`. -/
public theorem intResNat_cast {p : ℕ} {z : ℤ} (hp : p ≠ 0) :
    ((z % (p : ℤ)).toNat : ZMod p) = z := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (mod_cast hp)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

@[simp, grind =] lemma polyEval_cons {c u : ℤ} : polyEval (c :: cs) u = c + u * polyEval cs u := by
  simp [polyEval]

@[simp, grind =] lemma polyModL_cons {c : ℤ} :
    polyModL (c :: cs) ℓ r = ((c % ℓ).toNat + r * polyModL cs ℓ r) % ℓ := by simp [polyModL]

/-- A `polyModL` value is a residue mod `ℓ`. -/
public theorem polyModL_lt (hℓ : ℓ ≠ 0) : polyModL cs ℓ r < ℓ := by
  cases cs with
  | nil => exact hℓ.bot_lt
  | cons _ _ => exact Nat.mod_lt _ hℓ.bot_lt

/-- `polyModL` casts to `polyEval` in `ZMod ℓ`. -/
public theorem polyModL_cast (hl : ℓ ≠ 0) : (polyModL cs ℓ r : ZMod ℓ) = polyEval cs r := by
  induction cs with
  | nil => simp [polyModL, polyEval]
  | cons c t ih => simp [ih, intResNat_cast, hl]

/-- The `Nat` residue test at `r` passes exactly when `polyEval cs r` vanishes in `ZMod ℓ`
(`1 < ℓ`). -/
public theorem polyModL_beq (hℓ : 1 < ℓ) :
    (polyModL cs ℓ r).beq 0 ↔ (polyEval cs r : ZMod ℓ) = 0 := by
  rw [Nat.beq_eq, ← polyModL_cast (by lia), ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.mod_eq_of_lt (polyModL_lt (by lia))]

/-- `polyEval` is invariant, modulo `ℓ`, under changing its argument by a multiple of `ℓ`. -/
public theorem polyEval_modEq {a b : ℤ} (h : (a : ZMod ℓ) = b) :
    (polyEval cs a : ZMod ℓ) = polyEval cs b := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    rw [polyEval_cons, polyEval_cons]
    grind

/-- If the monic polynomial with lower coefficients `cs` has no root mod `ℓ` (with `1 < ℓ`), it has
no integer root. -/
public theorem no_int_root_of_monicHasNoRootMod (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod cs ℓ) (u : ℤ) : polyEval (cs ++ [1]) u ≠ 0 := by
  rw [monicHasNoRootMod, allBelow_iff] at h
  replace h : ∀ r < ℓ, (polyEval (cs ++ [1]) r : ZMod ℓ) ≠ 0 := by
    simp_rw [ne_eq, ← polyModL_beq hℓ, Bool.not_eq_true]
    grind
  intro hu
  have hℓ0 : (0 : ℤ) < ℓ := by positivity
  set r := u % ℓ with hr
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  refine h r.toNat (by grind) ?_
  rw [polyEval_modEq, hu, Int.cast_zero]
  simp [r, Int.emod_nonneg _ hℓ0.ne']

/-! ## Quadratic no-root lemmas (for the `t = 1` cofactor)

No-rational-root lemmas for the cofactor quadratic `q = X² + b X + c`, certified by a prime `ℓ`
modulo which `q` has no root. -/

open Polynomial in
/-- If the monic integer quadratic `x² + b x + c` has no root mod `ℓ` (with `1 < ℓ`), it has no
rational root. -/
public theorem no_rat_root_of_monicHasNoRootMod {b c : ℤ} (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [c, b] ℓ) {x : ℚ}
    (hx : x ^ 2 + b * x + c = 0) : False := by
  set p : ℤ[X] := X ^ 2 + C b * X + C c with hp
  have hmonic : p.Monic := by simp only [p]; monicity!
  have haeval : p.aeval x = x ^ 2 + b * x + c := by simp [hp]
  have hroot : p.aeval x = 0 := by grind
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  simp only [algebraMap_int_eq, eq_intCast] at hz
  refine no_int_root_of_monicHasNoRootMod hℓ h z ?_
  have hQ : (polyEval [c, b, 1] z : ℚ) = 0 := by
    simp only [polyEval]
    grind
  exact mod_cast hQ

end ECCompute
