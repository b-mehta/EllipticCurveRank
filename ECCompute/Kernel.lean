/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Kernel-reducible definitions

The kernel-reducible `Bool` checkers and the `Nat`/`Int`/`List` arithmetic they fold over. The
correctness proofs and the abstract-typed spec definitions live in `ECCompute.Soundness.*`.

Currently the `Bool` folds `allBelow`/`allList` and the 𝔽₂ matrix-inverse checker.
-/

namespace ECCompute

/-- Kernel-reducible bounded `∀`: `true` iff `p m = true` for every `m < n`. -/
noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  n.rec true fun m r ↦ (p m).and' r

/-- Kernel-reducible `∀` over a list: `true` iff `p a = true` for every `a ∈ l`. -/
noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r ↦ (p a).and' r

/-! ## 𝔽₂ matrix inverse -/

namespace F2Invert

/-- XOR of the low 32 bits of `v`, folded into bit 0 by five shift-xor stages (16, 8, 4, 2, 1).
For input `v < 2 ^ n` this equals the spec `popParity n v` (`popParityK_eq`), the range `checkInv`
enforces through `maskBelow`. -/
noncomputable def popParityK (v : Nat) : Bool :=
  let v := v.xor (v.shiftRight 16); let v := v.xor (v.shiftRight 8)
  let v := v.xor (v.shiftRight 4); let v := v.xor (v.shiftRight 2)
  let v := v.xor (v.shiftRight 1)
  (v.land 1).beq 1

/-- One row's contribution to the inverse check: for the row bitmask `bi` at row index `i`, fold
over the columns of `M`, comparing the parity of `bi &&& mₖ` (via `popParityK`) against the diagonal
indicator `i == k`. Soundness of the fold requires `bi, mₖ < 2 ^ n` with `n ≤ 32`, which `checkInv`
verifies separately. -/
noncomputable def checkInvRow (bi i k : Nat) (M : List Nat) : Bool :=
  M.rec (motive := fun _ ↦ Nat → Bool) (fun _ ↦ true)
    (fun m _ ih k ↦ ((popParityK (bi.land m)).rec (motive := fun _ ↦ Bool)
      (i.beq k).not' (i.beq k)).and' (ih k.succ)) k

/-- Fold over the rows of `B`, checking each against the columns of `M` with `checkInvRow`. -/
noncomputable def checkInvGo (M : List Nat) (i : Nat) (B : List Nat) : Bool :=
  B.rec (motive := fun _ ↦ Nat → Bool) (fun _ ↦ true)
    (fun b _ ih i ↦ (checkInvRow b i 0 M).and' (ih i.succ)) i

/-- Every mask in `L` fits in `n` bits (`< 2 ^ n`). -/
noncomputable def maskBelow (n : Nat) (L : List Nat) : Bool :=
  allList (fun x ↦ x.blt (Nat.shiftLeft 1 n)) L

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. Also verifies that all
masks fit in `n ≤ 32` bits, which `popParityK` relies on for soundness. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (maskBelow n B).and' ((maskBelow n M).and' ((n.ble 32).and' (checkInvGo M 0 B)))

end F2Invert

end ECCompute
