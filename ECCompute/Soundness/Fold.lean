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
`ECCompute.allList` (from `Kernel`) as a bounded `∀` and a list `∀`, and the `succ`/`cons` lemmas
peel one step.
-/

section

namespace ECCompute

section
variable {n : Nat} {p : Nat → Bool}

/-- `allBelow 0 p` is vacuously `true`. -/
@[simp] theorem allBelow_zero : allBelow 0 p = true := rfl

/-- `allBelow (n + 1) p` peels the top index: it folds `p n` into `allBelow n p`. -/
@[simp, grind =] theorem allBelow_succ : allBelow (n + 1) p = (p n).and' (allBelow n p) := rfl

/-- `allBelow` is `true` exactly when `p` holds at every `m < n`. -/
@[grind =] public theorem allBelow_iff : allBelow n p ↔ ∀ m < n, p m := by
  induction n with
  | zero => simp
  | succ k ih => rw [allBelow_succ, Bool.and'_eq_and, Bool.and_eq_true, ih]; grind

end

section
variable {α : Type} {p : α → Bool} {l : List α}

/-- `allList` over the empty list is `true`. -/
@[simp] theorem allList_nil : allList p [] = true := rfl

/-- `allList` peels the head element, folding `p a` into `allList p l`. -/
@[simp, grind =] theorem allList_cons {a : α} :
    allList p (a :: l) = (p a).and' (allList p l) := rfl

/-- `allList` computes the universal quantifier over the members of a list. -/
@[grind =] public theorem allList_iff : allList p l ↔ ∀ a ∈ l, p a := by
  induction l with
  | nil => simp
  | cons a t ih => rw [allList_cons, Bool.and'_eq_and, Bool.and_eq_true, ih, List.forall_mem_cons]

end

end ECCompute

end
