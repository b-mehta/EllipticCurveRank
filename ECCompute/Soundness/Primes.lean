/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Kernel
import ECCompute.Soundness.Fold
import ECCompute.ForLean
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith

/-!
# A kernel-reducible primality test for small numbers

`ECCompute.passes` is a trial-division fold (defined in `ECCompute.Kernel`), and
`Nat.prime_of_passes` certifies that if `n < 23² = 529` survives trial division by the primes below
`23`, then `n` is prime. It certifies the small label primes used by the rank certificates.

## Main results

* `Nat.primes_below_23`: the primes below `23` are exactly `[2, 3, 5, 7, 11, 13, 17, 19]`.
* `Nat.prime_of_passes`: if `2 ≤ n < 529` and `passes n [2, 3, 5, 7, 11, 13, 17, 19] = true`, then
  `Nat.Prime n`.
* `ECCompute.checkPrime_true` / `ECCompute.checkPrimes_true`: soundness of the kernel `Bool`
  checkers `checkPrime` / `checkPrimes`.
-/

namespace ECCompute

@[simp, grind =] theorem passes_nil (x : ℕ) : passes x [] := rfl

@[simp, grind =] theorem passes_cons (x a : ℕ) (t : List ℕ) :
    passes x (a :: t) = ((Nat.ble 1 (x % a)).or' (x.ble a)).and' (passes x t) := rfl

/-- `passes x L = true` exactly when every `i ∈ L` fails to be a proper divisor of `x`: either
`x % i ≠ 0` or `x ≤ i`. -/
theorem passes_true_iff {x : ℕ} {L : List ℕ} :
    passes x L ↔ ∀ i ∈ L, x % i ≠ 0 ∨ x ≤ i := by
  induction L with
  | nil => simp
  | cons a t ih => grind

/-- The primes below `23` are exactly `[2, 3, 5, 7, 11, 13, 17, 19]`. -/
theorem primes_below_23 (p : ℕ) (hlt : p < 23) (hp : p.Prime) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := by
  decide +revert +kernel

/-- If `2 ≤ n < 529 = 23²` and `n` survives trial division by the primes below `23`, then `n` is
prime. -/
theorem prime_of_passes (n : ℕ) (h2 : 2 ≤ n) (h529 : n < 529)
    (hpass : passes n [2, 3, 5, 7, 11, 13, 17, 19]) : Nat.Prime n := by
  by_contra hnp
  have hn0 : 0 < n := by lia
  set p := n.minFac
  have hpp : p.Prime := Nat.minFac_prime (by lia)
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
  have hplt23 : p < 23 := lt_of_pow_lt_pow_left' 2 (by grind)
  have hpmem : p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := primes_below_23 p hplt23 hpp
  have hpltn : p < n := by nlinarith [hpp.two_le, hsq]
  rcases (passes_true_iff.mp hpass) p hpmem with hmod | hle
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n))
  · lia

theorem checkPrime_true {p : ℕ} (h : checkPrime p) : p.Prime := by
  grind [checkPrime, prime_of_passes]

/-- If `checkPrimes` passes, every label's prime component really is prime. -/
theorem checkPrimes_true {ls : List (ℕ × ℤ)} (h : checkPrimes ls) :
    ∀ l ∈ ls, l.1.Prime := by
  grind [checkPrimes, checkPrime_true]

end ECCompute
