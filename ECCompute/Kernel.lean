/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Basic

/-!
# Kernel-reducible definitions

Every kernel-reducible `Bool` checker and the raw `Nat`/`Int` arithmetic it folds over, gathered in
one file so the whole trusted, kernel-reduced surface sits in one place with a deliberately small
import set. Nothing here mentions an abstract type (`ZMod`, `Matrix`, the `ℤ` ring `^`); those and
all correctness proofs live in `ECCompute.Soundness.*`.

So far: the bounded and structural `Bool` folds `anyBelow` and `allList`.
-/

namespace ECCompute

/-- Kernel-reducible bounded `∃`: `true` iff `p m = true` for some `m < n`. -/
noncomputable def anyBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec false (fun m r => (p m).or' r) n

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type*} (p : α → Bool) : List α → Bool :=
  List.rec true (fun a _ r => (p a).and' r)

end ECCompute
