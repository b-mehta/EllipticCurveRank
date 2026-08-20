/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Reducing an integer to a `Nat` residue before casting to `ZMod p`

`intResNat_cast` says the `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p`, and
`natCast_eq_zero_iff_of_lt` reads a vanishing cast back as an equation in `ℕ`. Together they take a
checker's `Nat` residue computation to a statement about the integer it stands for.

A checker is written in the raw arithmetic primitives, and its correctness proof works in the
notation `push_cast` and `ring` act on. Core names `Nat.add_eq`, `Nat.sub_eq`, `Nat.mul_eq`,
`Int.add_def` and `Int.mul_def` for the crossing; `Nat.mod_eq_mod`, `Int.sub_eq` and `Int.neg_eq`
complete that set.
-/

/-- The `Nat.mod` primitive is `%`. Core's counterpart for `Nat.add`, `Nat.sub` and `Nat.mul` is
`Nat.add_eq` and friends; `Nat.mod_eq` is the recursion equation, hence this name. -/
theorem Nat.mod_eq_mod (a b : ℕ) : Nat.mod a b = a % b := rfl

/-- The `Int.sub` primitive is `-`, matching `Nat.sub_eq` and core's own `Int.add_def`. -/
theorem Int.sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl

/-- The `Int.neg` primitive is unary `-`. -/
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
