/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import ECCompute.Check.Fold

/-!
# A kernel-reducible primality test for small numbers

`passes` is a trial-division fold, and `Nat.prime_of_passes` certifies that if `n < 23² = 529`
survives trial division by the primes below `23`, then `n` is prime. It certifies the small label
primes used by the rank certificates, one at a time through `checkPrime` and across a label list
through `checkPrimes`.

## Main definitions

* `ECCompute.passes`: the trial-division fold.
* `ECCompute.checkPrime`, `ECCompute.checkPrimes`: the kernel `Bool` primality check for one number
  and for every prime component of a label list.

## Main results

* `Nat.primes_below_23`: the primes below `23` are exactly `[2,3,5,7,11,13,17,19]`.
* `Nat.prime_of_passes`: if `2 ≤ n < 529` and `passes n [2,3,5,7,11,13,17,19] = true`, then
  `Nat.Prime n`.
* `ECCompute.checkPrime_true`, `ECCompute.checkPrimes_true`: the passage from the `Bool` checks to
  `Nat.Prime`.
-/

namespace ECCompute

/-- Trial division as a `Bool`-valued fold: `passes x L = true` iff no `i ∈ L` with `i < x`
divides `x`. -/
noncomputable def passes (x : ℕ) : List ℕ → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

/-- The empty divisor list passes vacuously. -/
@[simp] theorem passes_nil (x : ℕ) : passes x [] = true := rfl

/-- `passes` peels the head divisor, folding its test into `passes x t`. -/
private theorem passes_cons (x a : ℕ) (t : List ℕ) :
    passes x (a :: t) = ((Nat.ble 1 (x % a)).or' (Nat.ble x a)).and' (passes x t) := rfl

/-- `passes x L = true` exactly when every `i ∈ L` fails to be a proper divisor of `x`: either
`x % i ≠ 0` or `x ≤ i`. -/
theorem passes_true_iff {x : ℕ} {L : List ℕ} :
    passes x L = true ↔ ∀ i ∈ L, x % i ≠ 0 ∨ x ≤ i := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [passes_cons]
    simp only [Bool.and'_eq_and, Bool.or'_eq_or, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq]
    grind

/-- The primes below `23` are exactly `[2, 3, 5, 7, 11, 13, 17, 19]`. -/
theorem _root_.Nat.primes_below_23 (p : ℕ) (hlt : p < 23) (hp : p.Prime) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := by
  decide +revert +kernel

/-- If `2 ≤ n < 529 = 23²` and `n` survives trial division by the primes below `23`, then `n` is
prime. -/
theorem _root_.Nat.prime_of_passes (n : ℕ) (h2 : 2 ≤ n) (h529 : n < 529)
    (hpass : passes n [2, 3, 5, 7, 11, 13, 17, 19]) : Nat.Prime n := by
  by_contra hnp
  have hn0 : 0 < n := by lia
  set p := n.minFac
  have hpp : p.Prime := Nat.minFac_prime (by lia)
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
  have hplt23 : p < 23 := lt_of_pow_lt_pow_left' 2 (by grind)
  have hpmem : p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := Nat.primes_below_23 p hplt23 hpp
  have hpltn : p < n := by nlinarith [hpp.two_le, hsq]
  rcases (passes_true_iff.mp hpass) p hpmem with hmod | hle
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n))
  · lia

/-- Kernel `Bool`: `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`ECCompute.passes`). -/
noncomputable def checkPrime (p : ℕ) : Bool :=
  (Nat.ble 2 p).and' ((Nat.ble p 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

/-- If `checkPrime` passes, `p` really is prime. -/
theorem checkPrime_true {p : ℕ} (h : checkPrime p = true) : p.Prime := by
  simp only [checkPrime, Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, hle, hpass⟩ := h
  exact Nat.prime_of_passes p h2 (by lia) hpass

/-- Kernel `Bool`: every label's prime component passes `checkPrime`. -/
noncomputable def checkPrimes (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkPrime l.1) labels

/-- If `checkPrimes` passes, every label's prime component really is prime. -/
theorem checkPrimes_true {labels : List (ℕ × ℤ)} (h : checkPrimes labels = true) :
    ∀ l ∈ labels, (l.1).Prime := by
  rw [checkPrimes, allList_eq_true] at h
  exact fun l hl => checkPrime_true (h l hl)

end ECCompute
