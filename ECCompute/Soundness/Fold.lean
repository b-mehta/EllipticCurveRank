/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Basic
import ECCompute.Kernel

/-!
# Soundness of the `Bool` folds

`allBelow_eq_true` and `allList_eq_true` characterize the kernel folds `ECCompute.allBelow` and
`ECCompute.allList` (from `Kernel`) as a bounded `∀` and a list `∀`, the `succ`/`cons` lemmas peel
one step, and `Nat.beq_eq'` identifies `Nat.beq` with the `BEq`-dispatched `==`.
-/

namespace ECCompute

/-- `allBelow (n + 1) p` peels the top index: it folds `p n` into `allBelow n p`. -/
theorem allBelow_succ (n : Nat) (p : Nat → Bool) :
    allBelow (n + 1) p = (p n).and' (allBelow n p) := rfl

/-- `allBelow` is `true` exactly when `p` holds at every `m < n`. -/
theorem allBelow_eq_true {n : Nat} {p : Nat → Bool} :
    allBelow n p ↔ ∀ m < n, p m := by
  induction n with
  | zero => exact iff_of_true rfl (by simp)
  | succ k ih =>
    rw [allBelow_succ, Bool.and'_eq_and, Bool.and_eq_true, ih]
    grind

/-- `allList` peels the head element, folding `p a` into `allList p l`. -/
theorem allList_cons {α : Type} (p : α → Bool) (a : α) (l : List α) :
    allList p (a :: l) = (p a).and' (allList p l) := rfl

/-- `allList` computes the universal quantifier over the members of a list. -/
@[grind =] theorem allList_eq_true {α : Type} {p : α → Bool} {l : List α} :
    allList p l ↔ ∀ a ∈ l, p a := by
  induction l with
  | nil => simp [allList]
  | cons a t ih => rw [allList_cons, Bool.and'_eq_and, Bool.and_eq_true, ih, List.forall_mem_cons]

/-- `Nat.beq` and the `BEq`-dispatched `==` agree on `ℕ`. -/
theorem _root_.Nat.beq_eq' (a b : ℕ) : a.beq b = (a == b) := by
  cases hab : a == b <;> cases hnb : a.beq b <;> simp_all [beq_iff_eq, Nat.beq_eq]

end ECCompute
