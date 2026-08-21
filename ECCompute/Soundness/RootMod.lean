/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import ECCompute.Kernel
import ECCompute.Soundness.Fold
import ECCompute.Soundness.IntResNat
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

@[simp, grind =] lemma monicEval_cons {c u : ℤ} :
    monicEval (c :: cs) u = c + u * monicEval cs u := by
  simp [monicEval]

@[simp, grind =] lemma monicModL_cons {c : ℤ} :
    monicModL (c :: cs) ℓ r = ((c % ℓ).toNat + r * monicModL cs ℓ r) % ℓ := by
  simp [monicModL]

/-- A `monicModL` value is a residue mod `ℓ`. -/
theorem monicModL_lt (hℓ : 1 < ℓ) : monicModL cs ℓ r < ℓ := by
  cases cs with
  | nil => exact hℓ
  | cons _ _ => exact Nat.mod_lt _ (by grind)

/-- `monicModL` casts to `monicEval` in `ZMod ℓ`. -/
theorem monicModL_cast (hl : ℓ ≠ 0) : (monicModL cs ℓ r : ZMod ℓ) = monicEval cs r := by
  induction cs with
  | nil => simp [monicModL, monicEval]
  | cons c t ih => simp [ih, intResNat_cast, hl]

/-- The `Nat` residue test at `r` passes exactly when `monicEval cs r` vanishes in `ZMod ℓ`
(`1 < ℓ`). -/
theorem monicModL_beq (hℓ : 1 < ℓ) : (monicModL cs ℓ r).beq 0 ↔ (monicEval cs r : ZMod ℓ) = 0 := by
  rw [Nat.beq_eq, ← monicModL_cast (by lia), ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.mod_eq_of_lt (monicModL_lt hℓ)]

/-- `monicEval` is invariant, modulo `n`, under changing its argument by a multiple of `n`. -/
theorem monicEval_modEq {a b : ℤ} (h : (a : ZMod ℓ) = b) :
    (monicEval cs a : ZMod ℓ) = monicEval cs b := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    rw [monicEval_cons, monicEval_cons]
    grind

/-- If the monic polynomial has no root mod `ℓ` (with `1 < ℓ`), it has no integer root. -/
theorem no_int_root_of_monicHasNoRootMod (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod cs ℓ) (u : ℤ) : monicEval cs u ≠ 0 := by
  rw [monicHasNoRootMod, allBelow_eq_true] at h
  replace h : ∀ r < ℓ, (monicEval cs r : ZMod ℓ) ≠ 0 := by
    simp_rw [ne_eq, ← monicModL_beq hℓ, Bool.not_eq_true]
    simpa [Bool.not'_eq_not] using h
  intro hu
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast (by omega : (0 : ℕ) < ℓ)
  set r : ℤ := u % ℓ with hr
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  refine h r.toNat (by grind) ?_
  rw [monicEval_modEq, hu, Int.cast_zero]
  simp [r, Int.emod_nonneg _ hℓ0.ne']

/-! ## Quadratic no-root lemmas (for the `t = 1` cofactor)

No-rational-root lemmas for the cofactor quadratic `q = X² + b X + c`, certified by a prime `ℓ`
modulo which `q` has no root. -/

open Polynomial in
/-- If the monic integer quadratic `u² + b u + c` has no integer root, then it has no *rational*
root: by the rational root theorem, a rational root of a monic integer polynomial is an integer. -/
theorem no_rat_root_of_monicHasNoRootMod {b c : ℤ} (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [c, b] ℓ) (x : ℚ)
    (hx : x ^ 2 + b * x + c = 0) : False := by
  set p : ℤ[X] := X ^ 2 + C b * X + C c with hp
  have hmonic : p.Monic := by simp only [p]; monicity!
  have haeval : p.aeval x = x ^ 2 + b * x + c := by simp [hp]
  have hroot : p.aeval x = 0 := by grind
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  simp only [algebraMap_int_eq, eq_intCast] at hz
  refine no_int_root_of_monicHasNoRootMod hℓ h z ?_
  have hQ : (monicEval [c, b] z : ℚ) = 0 := by
    simp only [monicEval]
    grind
  exact mod_cast hQ

end ECCompute
