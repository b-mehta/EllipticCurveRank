/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Basic

/-!
# Kernel-reducible bounded and structural `Bool` folds

`anyBelow` folds a `Bool` predicate over `{m | m < n}` with the primed `Bool.or'` (via `Nat.rec`);
`allList` folds a predicate over the members of a `List` (via `List.rec`).  Phrasing the folds with
`Nat.rec`/`List.rec` and the primed connectives makes the kernel peel one index/element at a time —
which reduces far better than `(List.range n).all` / `List.all`, and never indexes a list
positionally.  These are the building blocks the certificate checkers (`checkB`, `checkInv`,
`checkPoints`, …) fold over.
-/

namespace ECCompute

/-- Kernel-reducible bounded `∃`: `true` iff `p m = true` for some `m < n`, phrased with `Nat.rec`
and the primed `Bool.or'` so the kernel peels one `m` at a time. `noncomputable` only because
`Bool.or'` is; the kernel reduces it regardless. -/
noncomputable def anyBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec false (fun m r => (p m).or' r) n

/-- `anyBelow (n + 1) p` peels the top index: it folds `p n` into `anyBelow n p`. -/
theorem anyBelow_succ (n : Nat) (p : Nat → Bool) :
    anyBelow (n + 1) p = (p n).or' (anyBelow n p) := rfl

/-- `anyBelow` is `false` exactly when `p` fails at every `m < n`. -/
theorem anyBelow_eq_false {n : Nat} {p : Nat → Bool} :
    anyBelow n p = false ↔ ∀ m, m < n → p m = false := by
  induction n with
  | zero => exact ⟨fun _ m hm => absurd hm (Nat.not_lt_zero m), fun _ => rfl⟩
  | succ k ih =>
    rw [anyBelow_succ, Bool.or'_eq_or, Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hk, hlt⟩ m hm
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hm) with h | h
      · exact hlt m h
      · exact h ▸ hk
    · exact fun h => ⟨h k (Nat.lt_succ_self k), fun m hm => h m (Nat.lt_succ_of_lt hm)⟩

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. Folds with the
primed `Bool.and'` via `List.rec`, so the kernel peels one element at a time and never indexes the
list positionally. `noncomputable` only because `Bool.and'` is; the kernel reduces it regardless. -/
noncomputable def allList {α : Type*} (p : α → Bool) : List α → Bool :=
  List.rec true (fun a _ r => (p a).and' r)

/-- `allList` peels the head element, folding `p a` into `allList p l`. -/
theorem allList_cons {α : Type*} (p : α → Bool) (a : α) (l : List α) :
    allList p (a :: l) = (p a).and' (allList p l) := rfl

/-- `allList` computes the universal quantifier over the members of a list. -/
theorem allList_eq_true {α : Type*} {p : α → Bool} {l : List α} :
    allList p l = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allList]
  | cons a t ih => rw [allList_cons, Bool.and'_eq_and, Bool.and_eq_true, ih, List.forall_mem_cons]

end ECCompute
