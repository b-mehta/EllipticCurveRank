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
# `p`-integral rationals

For a prime `p`, a rational is `p`-integral when it lies in the `p`-adic valuation ring,
equivalently `p ∤ q.den` (`Rat.mem_padicInteger_iff`). Membership is closed under the field
operations by the subring `add_mem`/`sub_mem`/`mul_mem`/`pow_mem`, with `Rat.inv_pIntegral` covering
division by a `p`-adic unit; `Rat.cast_{add,sub,mul}_of_pIntegral` reduce the field operations.

## Main results

* `Rat.IsPIntegral`, `Rat.mem_padicInteger_iff`: `p`-integrality as valuation-ring membership,
  matched with `(q.den : ZMod p) ≠ 0`.
* `Rat.den_cast_eq_zero_iff`, `Rat.ne_zero_of_den_eq_pow`: reductions of a power-base denominator
  `q.den = w ^ k`.
-/

section

namespace Rat

variable {p : ℕ}

/-- With `q.den = w ^ k` (`k ≠ 0`), the denominator vanishes mod `p` iff `w` does. -/
public theorem den_cast_eq_zero_iff [Fact p.Prime] {q : ℚ} {w k : ℕ} (hk : k ≠ 0)
    (hden : q.den = w ^ k) : (q.den : ZMod p) = 0 ↔ (w : ZMod p) = 0 := by
  rw [hden, Nat.cast_pow, pow_eq_zero_iff hk]

/-- If `q.den = w ^ k` with `k ≠ 0`, then `w ≠ 0`. -/
public theorem ne_zero_of_den_eq_pow {q : ℚ} {w k : ℕ} (hk : k ≠ 0) (hden : q.den = w ^ k) :
    w ≠ 0 := by
  rintro rfl; rw [zero_pow hk] at hden; exact q.den_nz hden

/-- A rational is `p`-integral, `x ∈ ℤ₍ₚ₎`, when it lies in the `p`-adic valuation ring. Stated
as subring membership so `add_mem`/`sub_mem`/`mul_mem`/`pow_mem` are the closure lemmas. -/
public abbrev IsPIntegral (p : ℕ) [Fact p.Prime] (x : ℚ) : Prop :=
  x ∈ (Rat.padicValuation p).integer

/-- A rational is `p`-integral iff its denominator is nonzero mod `p`. -/
public theorem mem_padicInteger_iff [Fact p.Prime] {x : ℚ} :
    IsPIntegral p x ↔ (x.den : ZMod p) ≠ 0 := by
  rw [IsPIntegral, Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff, Ne,
    ZMod.natCast_eq_zero_iff]

/-- Every integer is `p`-integral. -/
public theorem intCast_pIntegral [Fact p.Prime] (n : ℤ) : IsPIntegral p (n : ℚ) :=
  intCast_mem _ n

/-- On `p`-integral rationals the reduction is additive: `↑(x + y) = ↑x + ↑y`. -/
public theorem cast_add_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x + y : ℚ) : ZMod p) = (x : ZMod p) + (y : ZMod p) :=
  Rat.cast_add_of_ne_zero (mem_padicInteger_iff.mp hx) (mem_padicInteger_iff.mp hy)

/-- On `p`-integral rationals the reduction is subtractive: `↑(x - y) = ↑x - ↑y`. -/
public theorem cast_sub_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x - y : ℚ) : ZMod p) = (x : ZMod p) - (y : ZMod p) :=
  Rat.cast_sub_of_ne_zero (mem_padicInteger_iff.mp hx) (mem_padicInteger_iff.mp hy)

/-- On `p`-integral rationals the reduction is multiplicative: `↑(x * y) = ↑x * ↑y`. -/
public theorem cast_mul_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x * y : ℚ) : ZMod p) = (x : ZMod p) * (y : ZMod p) :=
  Rat.cast_mul_of_ne_zero (mem_padicInteger_iff.mp hx) (mem_padicInteger_iff.mp hy)

/-- The good-denominator property survives division by a rational that is nonzero mod `p`: the
inverse is `p`-integral because such a divisor is a `p`-adic unit. -/
public theorem inv_pIntegral [Fact p.Prime] {a : ℚ} (ha : IsPIntegral p a)
    (ha0 : (a : ZMod p) ≠ 0) : IsPIntegral p a⁻¹ := by
  have ha' : a ≠ 0 := fun h ↦ ha0 (by rw [h, Rat.cast_zero])
  rw [mem_padicInteger_iff, Rat.den_inv_of_ne_zero ha']
  have had := mem_padicInteger_iff.mp ha
  have hnum : (a.num : ZMod p) ≠ 0 := by
    rw [show (a.num : ZMod p) = (a : ZMod p) * (a.den : ZMod p) by
      rw [Rat.cast_def, div_mul_cancel₀ _ had]]
    exact mul_ne_zero ha0 had
  exact fun h ↦ hnum <| by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h

end Rat

end
