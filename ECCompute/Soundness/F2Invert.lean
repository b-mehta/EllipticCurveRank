/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Soundness.Fold
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import ECCompute.ForLean

/-!
# Soundness of the kernel-reducible 𝔽₂ matrix invertibility certificate

Correctness proofs for the `Bool` checker `ECCompute.F2Invert.checkInv` (defined in
`ECCompute.Kernel`): supplying a claimed inverse `M` (by rows) and checking `B * M = I` certifies
that the square matrix over `𝔽₂ = ZMod 2` interpreted from `B` is invertible. The row check
`invRowK i B[i] M` computes row `i` of `B * M` as the XOR of the rows of `M` selected by the set
bits of `B[i]`, and compares it to the unit vector `1 <<< i`.

## Main results

* `checkInv_isUnit` : `checkInv n B M → IsUnit (toMat B n)`, the invertibility certificate.
-/

namespace ECCompute.F2Invert

open Finset

variable {a b : Bool}

/-- `ZMod 2` indicator of a `Bool`: `true ↦ 1`, `false ↦ 0`. -/
def bId (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] lemma bId_false : bId false = 0 := rfl

lemma bId_inj (h : bId a = bId b) : a = b := by decide +revert +kernel
@[simp] lemma bId_xor : bId (a ^^ b) = bId a + bId b := by decide +revert +kernel
@[simp] lemma bId_and : bId (a && b) = bId a * bId b := by decide +revert +kernel

/-- The `Nat → Nat` fold inside `invRowK`: consuming `ms` one row at a time, XOR row `m` (when the
low bit of the running `b` is set) into the fold of the remaining rows over `b >>> 1`. -/
noncomputable def goRows (ms : List ℕ) (b : ℕ) : ℕ :=
  ms.rec (motive := fun _ ↦ ℕ → ℕ) (fun _ ↦ 0)
    (fun m _ ih b ↦ m * (b &&& 1) ^^^ ih (b >>> 1)) b

@[simp] theorem goRows_nil {b : ℕ} : goRows [] b = 0 := rfl

@[simp] theorem goRows_cons {m b : ℕ} {ms : List ℕ} :
    goRows (m :: ms) b = m * (b &&& 1) ^^^ goRows ms (b >>> 1) := rfl

/-- `invRowK` unfolds to the `beq` of the `goRows` fold against the unit vector `1 <<< i`. -/
theorem invRowK_eq {i bi : ℕ} {Mr : List ℕ} :
    invRowK i bi Mr = (goRows Mr bi).beq (1 <<< i) := rfl

/-- Bit `j` of one selected term `m * (b &&& 1)`, as a `ZMod 2` product: the low bit of `b` times
bit `j` of `m`. -/
private theorem bId_testBit_select {m b j : ℕ} :
    bId ((m * (b &&& 1)).testBit j) = bId (b.testBit 0) * bId (m.testBit j) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;>
    simp [Nat.and_one_is_mod, Nat.testBit_zero, h, bId]

/-- Bit `j` of the `goRows` fold, over `𝔽₂`: over each row `k`, the selector bit `b.testBit k` times
bit `j` of row `k`. -/
theorem bId_goRows_testBit {ms : List ℕ} {b j : ℕ} :
    bId ((goRows ms b).testBit j)
      = ∑ k ∈ range ms.length, bId (b.testBit k) * bId ((ms.getD k 0).testBit j) := by
  induction ms generalizing b with
  | nil => simp
  | cons m ms ih =>
    have hsum : (∑ k ∈ range ms.length, bId ((b >>> 1).testBit k) * bId ((ms.getD k 0).testBit j))
        = ∑ k ∈ range ms.length,
            bId (b.testBit (k + 1)) * bId (((m :: ms).getD (k + 1) 0).testBit j) :=
      Finset.sum_congr rfl fun k _ ↦ by
        rw [Nat.testBit_shiftRight, Nat.add_comm 1 k, List.getD_cons_succ]
    rw [goRows_cons, Nat.testBit_xor, bId_xor, ih, hsum, bId_testBit_select, List.length_cons,
      sum_range_succ', List.getD_cons_zero]
    abel

variable {n i i' : ℕ} {B M : List ℕ}

@[simp, grind =] theorem checkInvGo_cons {b : ℕ} {bs : List ℕ} :
    checkInvGo M i (b :: bs) = (invRowK i b M).and' (checkInvGo M i.succ bs) := rfl

/-- Interpret a `List Nat` of row bitmasks as an `n × n` matrix over `𝔽₂`. -/
public def toMat (B : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j ↦ if (B.getD i 0).testBit j then 1 else 0

/-- Entry `(i, j)` of `toMat B n`, for a row index in range: bit `j` of row `i` of `B`. -/
public theorem toMat_apply {B : List ℕ} {n : ℕ} {i j : Fin n} (h : i.val < B.length) :
    toMat B n i j = if B[i].testBit j then 1 else 0 := by
  rw [toMat, Matrix.of_apply, List.getD_eq_getElem _ _ h, Fin.getElem_fin]

/-- Entry `(i, j)` of `toMat B n` as the `𝔽₂` indicator of bit `j` of row `i`. -/
theorem toMat_eq_bId {B : List ℕ} {n : ℕ} {i j : Fin n} :
    toMat B n i j = bId ((B.getD i 0).testBit j) := rfl

/-- From a passing `checkInvGo` (started at row index `i`) the row check `invRowK` holds for every
row of `B`, at the shifted index `i + i'`. -/
theorem checkInvGo_true (hc : checkInvGo M i B) (hi' : i' < B.length) :
    invRowK (i + i') B[i'] M := by
  induction B generalizing i i' with
  | nil => simp at hi'
  | cons b bs ih =>
    rw [checkInvGo_cons, Bool.and'_eq_and, Bool.and_eq_true] at hc
    cases i' with
    | zero => simpa using hc.1
    | succ i'' =>
      have hidx : i + (i'' + 1) = i.succ + i'' := by omega
      rw [hidx, List.getElem_cons_succ]
      exact ih hc.2 (by simpa using hi')

/-- If the aggregate check `checkInv n B M` passes, the row check `invRowK i B[i] M` holds for every
row `i` of `B`. -/
theorem invRowK_true (hi : i < B.length) (h : checkInv n B M) : invRowK i B[i] M := by
  have hgo : checkInvGo M 0 B := by grind [checkInv]
  simpa using checkInvGo_true hgo hi

/-- If the kernel-reducible checker `checkInv n B M` returns `true` (and `B`, `M` have length `n`),
then the matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
public theorem checkInv_isUnit (hBlen : B.length = n) (hMlen : M.length = n) (h : checkInv n B M) :
    IsUnit (toMat B n) := by
  have key : toMat B n * toMat M n = 1 := by
    ext i k
    have hi : i.val < B.length := by rw [hBlen]; exact i.2
    have hrow : goRows M B[i.val] = 1 <<< i.val :=
      Nat.eq_of_beq_eq_true (invRowK_eq ▸ invRowK_true hi h)
    have hg := bId_goRows_testBit (ms := M) (b := B.getD i 0) (j := k)
    rw [hMlen] at hg
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [toMat_eq_bId]
    rw [Fin.sum_univ_eq_sum_range
      (fun x ↦ bId ((B.getD i 0).testBit x) * bId ((M.getD x 0).testBit k)) n, ← hg,
      List.getD_eq_getElem _ _ hi, hrow, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rcases eq_or_ne i k with h' | h' <;> simp [h', bId, Fin.val_inj]
  exact .of_mul_eq_one (toMat M n) key

end ECCompute.F2Invert
