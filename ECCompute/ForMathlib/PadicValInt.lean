/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Divisibility monotonicity of `padicValInt`

## Main results

* `padicValInt_le_padicValInt_of_dvd`: `padicValInt p` is monotone under divisibility with a
  nonzero target.

Destination: `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.
-/

variable (p : ℕ) [Fact p.Prime]

/-- `padicValInt p` is monotone under divisibility for a nonzero target. -/
theorem padicValInt_le_padicValInt_of_dvd {a b : ℤ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValInt p a ≤ padicValInt p b := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne a 0 with rfl | ha
  · simp [padicValInt]
  · simp only [padicValInt, ← Nat.factorization_def _ hp]
    exact (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr ha)
      (Int.natAbs_ne_zero.mpr hb)).mpr (Int.natAbs_dvd_natAbs.mpr hab) p
