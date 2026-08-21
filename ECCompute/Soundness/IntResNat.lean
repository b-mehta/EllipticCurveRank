/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Reducing an integer to a `Nat` residue before casting to `ZMod p`

These lemmas relate a checker's `Nat` residue computation to the integer it stands for, and its raw
arithmetic primitives to their notation.
-/

theorem Nat.mod_eq_mod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem Int.sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl

theorem Int.neg_eq (a : ℤ) : Int.neg a = -a := rfl

namespace ECCompute

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p`. -/
theorem intResNat_cast {p : ℕ} [NeZero p] (z : ℤ) :
    (((z % (p : ℤ)).toNat : ℕ) : ZMod p) = (z : ZMod p) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact_mod_cast (NeZero.ne p))
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

/-- A residue `n < p` is zero in `ZMod p` exactly when it is zero in `ℕ`. -/
theorem natCast_eq_zero_iff_of_lt {p n : ℕ} (h : n < p) : ((n : ℕ) : ZMod p) = 0 ↔ n = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨fun hd => Nat.eq_zero_of_dvd_of_lt hd h, fun hn => hn ▸ dvd_zero p⟩

end ECCompute
