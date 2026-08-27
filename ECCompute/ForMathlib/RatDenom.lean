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

* `Rat.den_add_ne_zero`, `Rat.den_sub_ne_zero`, `Rat.den_mul_ne_zero`, `Rat.den_pow_ne_zero`:
  closure of `(·.den : ZMod p) ≠ 0` under the field operations.
-/

section

namespace Rat

variable {p : ℕ}

/-- A rational lies in the `p`-adic valuation ring iff its denominator is nonzero mod `p`. -/
public theorem mem_padicInteger_iff [Fact p.Prime] {x : ℚ} :
    x ∈ (Rat.padicValuation p).integer ↔ (x.den : ZMod p) ≠ 0 := by
  rw [Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff, Ne, ZMod.natCast_eq_zero_iff]

variable {x y : ℚ}

/-- `(·.den : ZMod p) ≠ 0` is closed under addition. -/
public theorem den_add_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x + y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (add_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under subtraction. -/
public theorem den_sub_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x - y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (sub_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under multiplication. -/
public theorem den_mul_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x * y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (mul_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))

/-- `(·.den : ZMod p) ≠ 0` is closed under powers. -/
public theorem den_pow_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0) (n : ℕ) :
    ((x ^ n).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (pow_mem (mem_padicInteger_iff.mpr hx) n)


end Rat

end
