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

Correctness of the `Bool` checker `ECCompute.F2Invert.checkInv` (defined in `ECCompute.Kernel`):
a passing `checkInv B M`, with a claimed inverse `M` by rows, certifies that the square matrix over
`𝔽₂ = ZMod 2` interpreted from the rows of `B` is invertible.

## Main results

* `checkInv_isUnit` : `checkInv B M → IsUnit (toMat B n)`, the invertibility certificate.
-/

namespace ECCompute.F2Invert

open Finset

variable {a b : Bool}

/-- `ZMod 2` indicator of a `Bool`: `true ↦ 1`, `false ↦ 0`. -/
def bId (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] lemma bId_false : bId false = 0 := rfl

@[simp] lemma bId_xor : bId (a ^^ b) = bId a + bId b := by decide +revert +kernel
@[simp] lemma bId_and : bId (a && b) = bId a * bId b := by decide +revert +kernel

@[simp, grind =] theorem invRowK_nil {b : ℕ} : invRowK b [] = 0 := rfl

@[simp, grind =] theorem invRowK_cons {b m : ℕ} {ms : List ℕ} :
    invRowK b (m :: ms) = m * (b &&& 1) ^^^ invRowK (b >>> 1) ms := rfl

/-- Bit `j` of one selected term `m * (b &&& 1)`, as a `ZMod 2` product: the low bit of `b` times
bit `j` of `m`. -/
theorem bId_testBit_select {m b j : ℕ} :
    bId ((m * (b &&& 1)).testBit j) = bId (b.testBit 0) * bId (m.testBit j) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;>
    simp [Nat.and_one_is_mod, Nat.testBit_zero, h, bId]

/-- Bit `j` of `invRowK`, over `𝔽₂`: over each row `k`, the selector bit `b.testBit k` times
bit `j` of row `k`. -/
theorem bId_invRowK_testBit {ms : List ℕ} {b j : ℕ} :
    bId ((invRowK b ms).testBit j)
      = ∑ k ∈ range ms.length, bId (b.testBit k) * bId ((ms.getD k 0).testBit j) := by
  induction ms generalizing b with
  | nil => simp
  | cons m ms ih =>
    simp only [invRowK_cons, Nat.testBit_xor, bId_xor, ih, bId_testBit_select, List.length_cons,
      sum_range_succ', List.getD_cons_zero, List.getD_cons_succ, Nat.testBit_shiftRight,
      Nat.add_comm 1]
    abel

variable {n i i' : ℕ} {B M : List ℕ}

@[simp, grind =] theorem checkInvGo_cons {b : ℕ} {bs : List ℕ} :
    checkInvGo M i (b :: bs) = ((invRowK b M).beq (1 <<< i)).and' (checkInvGo M i.succ bs) := rfl

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

/-- From a passing `checkInvGo` (started at row index `i`), the row `invRowK B[i'] M` equals the
unit vector `1 <<< (i + i')` for every row of `B`. -/
theorem checkInvGo_true (hc : checkInvGo M i B) (hi' : i' < B.length) :
    invRowK B[i'] M = 1 <<< (i + i') := by
  induction B generalizing i i' with
  | nil => simp at hi'
  | cons b bs ih => cases i' <;> grind

/-- If the aggregate check `checkInv B M` passes, row `invRowK B[i] M` equals the unit vector
`1 <<< i` for every row `i` of `B`. -/
theorem invRowK_true (hi : i < B.length) (h : checkInv B M) : invRowK B[i] M = 1 <<< i := by
  have hgo : checkInvGo M 0 B := by grind [checkInv]
  simpa using checkInvGo_true hgo hi

/-- If the kernel-reducible checker `checkInv B M` returns `true` (and `B`, `M` have length `n`),
then the matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
public theorem checkInv_isUnit (hBlen : B.length = n) (hMlen : M.length = n) (h : checkInv B M) :
    IsUnit (toMat B n) := by
  have key : toMat B n * toMat M n = 1 := by
    ext i k
    have hi : i.val < B.length := by rw [hBlen]; exact i.2
    have hrow : invRowK B[i.val] M = 1 <<< i.val := invRowK_true hi h
    have hg := bId_invRowK_testBit (ms := M) (b := B.getD i 0) (j := k)
    rw [hMlen] at hg
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [toMat_eq_bId]
    rw [Fin.sum_univ_eq_sum_range
      (fun x ↦ bId ((B.getD i 0).testBit x) * bId ((M.getD x 0).testBit k)) n, ← hg,
      List.getD_eq_getElem _ _ hi, hrow, Nat.one_shiftLeft, Nat.testBit_two_pow]
    rcases eq_or_ne i k with h' | h' <;> simp [h', bId, Fin.val_inj]
  exact .of_mul_eq_one (toMat M n) key

end ECCompute.F2Invert
