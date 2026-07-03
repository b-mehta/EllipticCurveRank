/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A cheap kernel-reducible primality test for small numbers

This file provides `passes`, a trial-division fold, and a bound theorem certifying that if
`n < 23² = 529` survives trial division by the primes below `23`, then `n` is prime.  The point
is that `passes n [2,3,5,7,11,13,17,19]` reduces cheaply in the kernel (a short fold over
`Nat.mod`/`Nat.ble`), giving a fast primality certificate for the small label primes used by the
rank certificates.

## Main statements

* `Nat.primes_below_23` — the primes below `23` are exactly `[2,3,5,7,11,13,17,19]`.
* `Nat.prime_of_passes` — if `2 ≤ n < 529` and `passes n [2,3,5,7,11,13,17,19] = true`, then
  `Nat.Prime n`.
-/

namespace ECCompute

/-- Trial division as a `Bool`-valued fold: `passes x L = true` iff no `i ∈ L` with `i < x`
divides `x`.  For each `i`, `Nat.ble 1 (x.mod i)` says `x % i ≠ 0` (i.e. `i ∤ x`) and `x.ble i`
says `x ≤ i`; the whole fold is the conjunction over `L` of these disjunctions.  It is
`noncomputable` on purpose: the kernel reduces the primed `Bool` operations directly. -/
noncomputable def passes (x : ℕ) : List ℕ → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

@[simp] theorem passes_nil (x : ℕ) : passes x [] = true := rfl

theorem passes_cons (x a : ℕ) (t : List ℕ) :
    passes x (a :: t) = ((Nat.ble 1 (x % a)).or' (Nat.ble x a)).and' (passes x t) := rfl

/-- `passes x L = true` exactly when every `i ∈ L` fails to be a proper divisor of `x`: either
`x % i ≠ 0` or `x ≤ i`. -/
theorem passes_true_iff {x : ℕ} {L : List ℕ} :
    passes x L = true ↔ ∀ i ∈ L, x % i ≠ 0 ∨ x ≤ i := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [passes_cons]
    simp only [Bool.and'_eq_and, Bool.or'_eq_or, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq,
      List.mem_cons, forall_eq_or_imp, ih]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.imp (fun h ↦ by omega) id, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.imp (fun h ↦ by omega) id, h2⟩

/-- The primes below `23` are exactly `[2, 3, 5, 7, 11, 13, 17, 19]`. -/
theorem _root_.Nat.primes_below_23 (p : ℕ) (hp : p.Prime) (hlt : p < 23) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := by
  have h2 := hp.two_le
  interval_cases p <;> revert hp <;> decide

/-- If `2 ≤ n < 529 = 23²` and `n` survives trial division by the primes below `23`, then `n` is
prime.  A composite `n` has a prime factor `p ≤ √n < 23`, hence `p ∈ [2,3,5,7,11,13,17,19]` and
`p ∣ n` with `p < n`, so `passes n … = false` — contradiction. -/
theorem _root_.Nat.prime_of_passes (n : ℕ) (h2 : 2 ≤ n) (h529 : n < 529)
    (hpass : passes n [2, 3, 5, 7, 11, 13, 17, 19] = true) : Nat.Prime n := by
  by_contra hnp
  have hn0 : 0 < n := by omega
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
  have hplt23 : p < 23 := by
    by_contra hge
    have h23 : (23 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (Nat.not_lt.mp hge) 2
    norm_num at h23
    omega
  have hpmem : p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := Nat.primes_below_23 p hpp hplt23
  have hpltn : p < n := by nlinarith [hpp.two_le, hsq]
  rcases (passes_true_iff.mp hpass) p hpmem with hmod | hle
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp hpdvd)
  · omega

end ECCompute
