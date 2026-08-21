/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Basic
import ECCompute.Kernel

/-!
# Soundness of the `Bool` folds

`anyBelow_eq_false` and `allList_eq_true` characterize the kernel folds `ECCompute.anyBelow` and
`ECCompute.allList` (from `Kernel`) as a bounded `∃` and a list `∀`; the `succ`/`cons` lemmas peel
one step, and `natBeqEq` relates `Nat.beq` to the `BEq`-dispatched `==`.
-/

namespace ECCompute

/-- `anyBelow (n + 1) p` peels the top index: it folds `p n` into `anyBelow n p`. -/
theorem anyBelow_succ (n : Nat) (p : Nat → Bool) :
    anyBelow (n + 1) p = (p n).or' (anyBelow n p) := rfl

/-- `anyBelow` is `false` exactly when `p` fails at every `m < n`. -/
theorem anyBelow_eq_false {n : Nat} {p : Nat → Bool} :
    anyBelow n p = false ↔ ∀ m, m < n → p m = false := by
  induction n with
  | zero => exact iff_of_true rfl (by simp)
  | succ k ih =>
    rw [anyBelow_succ, Bool.or'_eq_or, Bool.or_eq_false_iff, ih]
    grind

/-- `allList` peels the head element, folding `p a` into `allList p l`. -/
theorem allList_cons {α : Type*} (p : α → Bool) (a : α) (l : List α) :
    allList p (a :: l) = (p a).and' (allList p l) := rfl

/-- `allList` computes the universal quantifier over the members of a list. -/
theorem allList_eq_true {α : Type*} {p : α → Bool} {l : List α} :
    allList p l = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allList]
  | cons a t ih => rw [allList_cons, Bool.and'_eq_and, Bool.and_eq_true, ih, List.forall_mem_cons]

/-- `Nat.beq` agrees with the `BEq`-dispatched `==` on `ℕ`. -/
theorem natBeqEq (a b : ℕ) : (a == b) = Nat.beq a b := by
  cases hab : a == b <;> cases hnb : Nat.beq a b <;> simp_all [beq_iff_eq, Nat.beq_eq]

end ECCompute
