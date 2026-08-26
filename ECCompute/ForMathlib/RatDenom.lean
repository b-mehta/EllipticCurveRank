/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.ZMod

import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Good denominators mod a prime

For a prime `p`, the "good denominator" predicate `(q.den : ZMod p) ≠ 0` on `ℚ` says that `q` lies
in the `p`-adic valuation ring `(Rat.padicValuation p).integer` (`Rat.mem_padicInteger_iff`), so it
is closed under the field operations through that subring.

## Main results

* `Rat.den_add_ne_zero`, `Rat.den_sub_ne_zero`, `Rat.den_mul_ne_zero`, `Rat.den_div_ne_zero`:
  closure of `(·.den : ZMod p) ≠ 0` under the field operations.
* `Rat.den_cast_eq_zero_iff`: reduces a power-base denominator `q.den = w ^ k` mod `p` to its base.
-/

section

namespace Rat

variable {p : ℕ}

/-- With `q.den = w ^ k` (`k ≠ 0`), the denominator vanishes mod `p` iff `w` does. -/
public theorem den_cast_eq_zero_iff [Fact p.Prime] {q : ℚ} {w k : ℕ} (hk : k ≠ 0)
    (hden : q.den = w ^ k) : (q.den : ZMod p) = 0 ↔ (w : ZMod p) = 0 := by
  rw [hden, Nat.cast_pow, pow_eq_zero_iff hk]

/-- A rational lies in the `p`-adic valuation ring iff its denominator is nonzero mod `p`. -/
public theorem mem_padicInteger_iff [Fact p.Prime] {x : ℚ} :
    x ∈ (Rat.padicValuation p).integer ↔ (x.den : ZMod p) ≠ 0 := by
  rw [Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff, Ne, ZMod.natCast_eq_zero_iff]

/-- `(·.den : ZMod p) ≠ 0` is closed under addition. -/
public theorem den_add_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x + y).den : ZMod p) ≠ 0 :=
  mem_padicInteger_iff.mp (add_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under subtraction. -/
public theorem den_sub_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x - y).den : ZMod p) ≠ 0 :=
  mem_padicInteger_iff.mp (sub_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under multiplication. -/
public theorem den_mul_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x * y).den : ZMod p) ≠ 0 :=
  mem_padicInteger_iff.mp (mul_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under division by an element nonzero mod `p`, since then the
inverse also has good denominator. -/
public theorem den_div_ne_zero [Fact p.Prime] {a b : ℚ} (hb : (b.den : ZMod p) ≠ 0)
    (ha : (a.den : ZMod p) ≠ 0) (ha0 : (a : ZMod p) ≠ 0) :
    ((b / a).den : ZMod p) ≠ 0 := by
  have ha' : a ≠ 0 := by grind [Rat.cast_zero]
  have hnum : (a.num : ZMod p) ≠ 0 := by
    have hval : (a.num : ZMod p) = a * a.den := by rw [Rat.cast_def, div_mul_cancel₀ _ ha]
    grind
  have hinv : (a⁻¹.den : ZMod p) ≠ 0 := by
    rwa [Rat.den_inv_of_ne_zero ha', ne_eq, ZMod.natCast_eq_zero_iff, ← Int.natCast_dvd_natCast,
      Int.dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [div_eq_mul_inv]; exact den_mul_ne_zero hb hinv

end Rat

end
