/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Kernel

import Mathlib.Data.List.Basic

/-!
# Soundness of the `Bool` folds

`allBelow_iff` and `allList_iff` characterize the kernel folds `ECCompute.allBelow` and
`ECCompute.allList` (from `Kernel`) as a bounded `∀` and a list `∀`, the `succ`/`cons` lemmas peel
one step, and `Nat.beq_eq'` identifies `Nat.beq` with the `BEq`-dispatched `==`.
-/

section

namespace ECCompute

/-- `allBelow 0 p` is vacuously `true`. -/
@[simp] theorem allBelow_zero {p : Nat → Bool} : allBelow 0 p = true := rfl

/-- `allBelow (n + 1) p` peels the top index: it folds `p n` into `allBelow n p`. -/
@[simp, grind =] theorem allBelow_succ {n : Nat} {p : Nat → Bool} :
    allBelow (n + 1) p = (p n).and' (allBelow n p) := rfl

/-- `allBelow` is `true` exactly when `p` holds at every `m < n`. -/
@[grind =] public theorem allBelow_iff {n : Nat} {p : Nat → Bool} :
    allBelow n p ↔ ∀ m < n, p m := by
  induction n with
  | zero => simp
  | succ k ih => rw [allBelow_succ, Bool.and'_eq_and, Bool.and_eq_true, ih]; grind

/-- `allList` over the empty list is `true`. -/
@[simp] theorem allList_nil {α : Type} {p : α → Bool} : allList p [] = true := rfl

/-- `allList` peels the head element, folding `p a` into `allList p l`. -/
@[simp, grind =] theorem allList_cons {α : Type} {p : α → Bool} {a : α} {l : List α} :
    allList p (a :: l) = (p a).and' (allList p l) := rfl

/-- `allList` computes the universal quantifier over the members of a list. -/
@[grind =] public theorem allList_iff {α : Type} {p : α → Bool} {l : List α} :
    allList p l ↔ ∀ a ∈ l, p a := by
  induction l with
  | nil => simp
  | cons a t ih => rw [allList_cons, Bool.and'_eq_and, Bool.and_eq_true, ih, List.forall_mem_cons]

/-- `Nat.beq` and the `BEq`-dispatched `==` agree on `ℕ`. -/
public theorem _root_.Nat.beq_eq' (a b : ℕ) : a.beq b = (a == b) := by
  cases hab : a == b <;> cases hnb : a.beq b <;> simp_all [beq_iff_eq, Nat.beq_eq]

end ECCompute

end
