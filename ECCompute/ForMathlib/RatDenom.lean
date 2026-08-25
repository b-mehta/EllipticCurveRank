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
equivalently `p ∤ q.den` (`Rat.mem_padicInteger_iff`). Reduction mod `p` is the ring hom
`Rat.padicReduce` on that subring, so subring `mem`/`map` lemmas handle the field operations;
`Rat.inv_pIntegral` covers division by a `p`-adic unit.

## Main results

* `Rat.IsPIntegral`, `Rat.mem_padicInteger_iff`, `Rat.padicReduce`: `p`-integrality as
  valuation-ring membership and reduction as its residue ring hom.
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

/-- Reduction mod `p` as a ring homomorphism from the `p`-adic valuation ring to `ZMod p`, the
rational cast restricted to `p`-integral rationals. `map_add`/`map_mul`/`map_pow` distribute the
reduction with no side conditions. -/
@[expose] public noncomputable def padicReduce (p : ℕ) [Fact p.Prime] :
    (Rat.padicValuation p).integer →+* ZMod p where
  toFun x := ((x : ℚ) : ZMod p)
  map_one' := by simp
  map_zero' := by simp
  map_mul' x y := by
    have hx := mem_padicInteger_iff.mp x.2
    have hy := mem_padicInteger_iff.mp y.2
    simpa only [Subring.coe_mul] using Rat.cast_mul_of_ne_zero hx hy
  map_add' x y := by
    have hx := mem_padicInteger_iff.mp x.2
    have hy := mem_padicInteger_iff.mp y.2
    simpa only [Subring.coe_add] using Rat.cast_add_of_ne_zero hx hy

@[simp] public theorem padicReduce_apply [Fact p.Prime] (x : (Rat.padicValuation p).integer) :
    padicReduce p x = ((x : ℚ) : ZMod p) := rfl

/-- Every integer is `p`-integral. -/
public theorem intCast_pIntegral [Fact p.Prime] (n : ℤ) : IsPIntegral p (n : ℚ) :=
  intCast_mem _ n

/-- On `p`-integral rationals the reduction is additive: `↑(x + y) = ↑x + ↑y`. -/
public theorem cast_add_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x + y : ℚ) : ZMod p) = (x : ZMod p) + (y : ZMod p) := by
  simpa using map_add (padicReduce p) ⟨x, hx⟩ ⟨y, hy⟩

/-- On `p`-integral rationals the reduction is subtractive: `↑(x - y) = ↑x - ↑y`. -/
public theorem cast_sub_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x - y : ℚ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  simpa using map_sub (padicReduce p) ⟨x, hx⟩ ⟨y, hy⟩

/-- On `p`-integral rationals the reduction is multiplicative: `↑(x * y) = ↑x * ↑y`. -/
public theorem cast_mul_of_pIntegral [Fact p.Prime] {x y : ℚ} (hx : IsPIntegral p x)
    (hy : IsPIntegral p y) : ((x * y : ℚ) : ZMod p) = (x : ZMod p) * (y : ZMod p) := by
  simpa using map_mul (padicReduce p) ⟨x, hx⟩ ⟨y, hy⟩

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
