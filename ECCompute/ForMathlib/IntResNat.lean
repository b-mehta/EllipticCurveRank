/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Reducing an integer to a `Nat` residue before casting to `ZMod p`

`intResNat_cast` says the `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p`.
-/

namespace ECCompute

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p` (for `0 < p`). -/
theorem intResNat_cast {p : ℕ} (hp : 0 < p) (z : ℤ) :
    (((z % (p : ℤ)).toNat : ℕ) : ZMod p) = (z : ZMod p) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact_mod_cast hp.ne')
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

end ECCompute
