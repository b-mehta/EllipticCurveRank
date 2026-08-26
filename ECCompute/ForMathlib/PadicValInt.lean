/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import Mathlib.Data.Nat.Factorization.Defs

/-!
# Divisibility bounds for `padicValInt`

Monotonicity of `padicValInt p` under divisibility, and a strict inequality read off an integer
product identity.

## Main results

* `padicValInt_mono`: `padicValInt p` is monotone under divisibility with a nonzero target.
* `padicValInt_lt_of_mul_eq`: from `N * S = K * W` with `p ∣ S`, `¬ p ∣ W` and nonzero factors,
  `v_p(N) < v_p(K)`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

/-- `padicValInt p` is monotone under divisibility for a nonzero target. -/
theorem padicValInt_mono {a b : ℤ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValInt p a ≤ padicValInt p b := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne a 0 with rfl | ha
  · simp [padicValInt]
  · simp only [padicValInt, ← Nat.factorization_def _ hp]
    exact (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr ha)
      (Int.natAbs_ne_zero.mpr hb)).mpr (Int.natAbs_dvd_natAbs.mpr hab) p

/-- From the integer identity `N * S = K * W` with `p ∣ S`, `¬ p ∣ W` and all factors nonzero,
conclude `v_p(N) < v_p(K)`. -/
theorem padicValInt_lt_of_mul_eq {N S K W : ℤ} (hid : N * S = K * W)
    (hpS : (p : ℤ) ∣ S) (hpW : ¬ (p : ℤ) ∣ W)
    (hN0 : N ≠ 0) (hS0 : S ≠ 0) (hK0 : K ≠ 0) (hW0 : W ≠ 0) :
    padicValInt p N < padicValInt p K := by
  have hSval : 1 ≤ padicValInt p S :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hS0)
      (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpS))
  have e1 := padicValInt.mul (p := p) hN0 hS0
  rw [hid, padicValInt.mul (p := p) hK0 hW0, padicValInt.eq_zero_of_not_dvd hpW] at e1
  lia
