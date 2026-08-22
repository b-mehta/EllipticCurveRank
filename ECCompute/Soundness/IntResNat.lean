/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Reducing an integer to a `Nat` residue before casting to `ZMod p`

These lemmas take a checker's `Nat` residue computation to a statement about the integer it stands
for.
-/

namespace ECCompute

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p`. -/
theorem intResNat_cast {p : ℕ} (hp : p ≠ 0) (z : ℤ) :
    ((z % (p : ℤ)).toNat : ZMod p) = (z : ZMod p) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact mod_cast hp)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

end ECCompute
