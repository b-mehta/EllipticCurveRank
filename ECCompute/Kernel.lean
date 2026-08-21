/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Kernel-reducible definitions

The kernel-reducible `Bool` checkers and the `Nat`/`Int`/`List` arithmetic they fold over. The
correctness proofs and the abstract-typed spec definitions live in `ECCompute.Soundness.*`.

Currently the `Bool` folds `anyBelow` and `allList`.
-/

namespace ECCompute

/-- Kernel-reducible bounded `∃`: `true` iff `p m = true` for some `m < n`. -/
noncomputable def anyBelow (n : Nat) (p : Nat → Bool) : Bool :=
  n.rec false fun m r => (p m).or' r

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r => (p a).and' r

end ECCompute
