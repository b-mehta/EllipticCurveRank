/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.ZMod

import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Lemmas

/-!
# Good denominators mod a prime

For a prime `p`, the "good denominator" predicate `(q.den : ZMod p) ≠ 0` on `ℚ` is closed under
the field operations. These lemmas transfer that survival through addition, subtraction,
multiplication, powers and division.

## Main results

* `Rat.den_add_ne_zero`, `Rat.den_sub_ne_zero`, `Rat.den_mul_ne_zero`, `Rat.den_pow_ne_zero`,
  `Rat.den_div_ne_zero`: closure of `(·.den : ZMod p) ≠ 0` under the field operations.
* `Rat.den_cast_eq_zero_iff`: reductions of a power-base denominator
  `q.den = w ^ k`.
-/

section

namespace ZMod

variable {p : ℕ}

/-- If `a ∣ b` and `b`'s reduction mod `p` is nonzero, so is `a`'s. -/
theorem natCast_ne_zero_of_dvd {a b : ℕ} (h : a ∣ b) (hb : (b : ZMod p) ≠ 0) :
    (a : ZMod p) ≠ 0 := fun ha =>
  hb ((ZMod.natCast_eq_zero_iff b p).mpr (((ZMod.natCast_eq_zero_iff a p).mp ha).trans h))

end ZMod

namespace Rat

variable {p : ℕ}

/-- With `q.den = w ^ k` (`k ≠ 0`), the denominator vanishes mod `p` iff `w` does. -/
public theorem den_cast_eq_zero_iff [Fact p.Prime] {q : ℚ} {w k : ℕ} (hk : k ≠ 0)
    (hden : q.den = w ^ k) : (q.den : ZMod p) = 0 ↔ (w : ZMod p) = 0 := by
  rw [hden, Nat.cast_pow, pow_eq_zero_iff hk]

/-- If `x` and `y` both reduce well mod `p`, so does `x + y`: the sum's denominator divides
`x.den * y.den`. -/
public theorem den_add_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x + y).den : ZMod p) ≠ 0 :=
  ZMod.natCast_ne_zero_of_dvd (Rat.add_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- Same for `x - y`, via `Rat.sub_den_dvd`. -/
public theorem den_sub_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x - y).den : ZMod p) ≠ 0 :=
  ZMod.natCast_ne_zero_of_dvd (Rat.sub_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- ... and for the product `x * y`. -/
public theorem den_mul_ne_zero [Fact p.Prime] {x y : ℚ} (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x * y).den : ZMod p) ≠ 0 :=
  ZMod.natCast_ne_zero_of_dvd (Rat.mul_den_dvd x y) (by rw [Nat.cast_mul]; exact mul_ne_zero hx hy)

/-- Powers `x ^ n` inherit the property from the multiplicative case. -/
public theorem den_pow_ne_zero [Fact p.Prime] {x : ℚ} (hx : (x.den : ZMod p) ≠ 0) (n : ℕ) :
    ((x ^ n).den : ZMod p) ≠ 0 := by
  rw [Rat.den_pow, Nat.cast_pow]
  exact pow_ne_zero n hx

/-- Division `b / a` too, as long as the divisor `a` reduces to a nonzero element (otherwise
`a⁻¹` need not have good denominator). -/
public theorem den_div_ne_zero [Fact p.Prime] {a b : ℚ} (hb : (b.den : ZMod p) ≠ 0)
    (ha : (a.den : ZMod p) ≠ 0) (ha0 : (a : ZMod p) ≠ 0) :
    ((b / a).den : ZMod p) ≠ 0 := by
  have ha' : a ≠ 0 := fun h => ha0 (by rw [h, Rat.cast_zero])
  have hnum : (a.num : ZMod p) ≠ 0 := by
    have hval : (a.num : ZMod p) = (a : ZMod p) * (a.den : ZMod p) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ ha]
    rw [hval]
    exact mul_ne_zero ha0 ha
  have hnatabs : ((a.num.natAbs : ℕ) : ZMod p) ≠ 0 := fun h => hnum <| by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  rw [div_eq_mul_inv]
  refine ZMod.natCast_ne_zero_of_dvd (Rat.mul_den_dvd b a⁻¹) ?_
  rw [Nat.cast_mul, Rat.den_inv_of_ne_zero ha']
  exact mul_ne_zero hb hnatabs

end Rat

end
