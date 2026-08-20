/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.List.Basic

/-!
# `List.getD` at an in-range index

## Main results

* `List.getD_mem_of_lt`: `l.getD n d` is a member of `l` when `n < l.length`.
* `List.getD_zipWith`: `getD` commutes with `zipWith` on equal-length lists at an in-range index.

Destination: `Mathlib/Data/List/Basic.lean`.
-/

namespace List

variable {α β γ : Type*}

/-- `l.getD n d` is a genuine member of `l` when the index is in range. -/
theorem getD_mem_of_lt {l : List α} {n : ℕ} {d : α} (h : n < l.length) : l.getD n d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- `getD` commutes with `zipWith` on equal-length lists at an in-range index. -/
theorem getD_zipWith (f : α → β → γ) (as : List α) (bs : List β) (n : ℕ)
    (da : α) (db : β) (dc : γ) (hn : n < as.length) (hlen : as.length = bs.length) :
    (List.zipWith f as bs).getD n dc = f (as.getD n da) (bs.getD n db) := by
  induction as generalizing bs n with
  | nil => simp at hn
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih bs n (by simpa using hn) (by simpa using hlen)

end List
