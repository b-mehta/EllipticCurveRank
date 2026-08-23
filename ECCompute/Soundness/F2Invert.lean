/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness.Fold
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Range
import ECCompute.ForLean

/-!
# Soundness of the kernel-reducible 𝔽₂ matrix invertibility certificate

Correctness proofs for the `Bool` checker `ECCompute.F2Invert.checkInv` (defined in
`ECCompute.Kernel`): supplying a claimed inverse `M` and checking `B * M = I` certifies that the
square matrix over `𝔽₂ = ZMod 2` interpreted from `B` is invertible.

## Main results

* `checkInv_true` : a passing `checkInv` gives, at each `(i, k)`, the diagonal parity indicator.
* `checkInv_isUnit` : `checkInv n B M → IsUnit (toMat B n)`, the invertibility certificate.
-/

namespace ECCompute.F2Invert

open Finset

variable {v : ℕ} {a b : Bool}

/-- Parity of the popcount of `a`, reading the low `fuel` bits. -/
def popParity : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, a => (a.testBit 0).xor (popParity fuel (a / 2))

/-- The XOR over `v.testBit j` for `j` in a list. -/
private def xorBits (v : ℕ) (l : List ℕ) : Bool :=
  l.foldr (fun j r ↦ (v.testBit j).xor r) false

private theorem land_one_beq_one : (v &&& 1 == 1) = v.testBit 0 := by
  grind

/-- `popParity fuel a` is the XOR over the low `fuel` bits of `a` (indices `0 … fuel-1`). -/
theorem popParity_eq_xorBits (fuel a : ℕ) :
    popParity fuel a = xorBits a (List.range fuel) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    rw [popParity, ih, List.range_succ_eq_map]
    simp only [xorBits, List.foldr_cons, List.foldr_map, Nat.testBit_zero, Nat.testBit_succ]

/-- Dropping trailing indices whose bit is `false` does not change the XOR. -/
private theorem xorBits_range_hi {n m : ℕ} (hzero : ∀ j, n ≤ j → v.testBit j = false)
    (hnm : n ≤ m) :
    xorBits v (List.range m) = xorBits v (List.range n) := by
  induction m with grind [List.range_succ, xorBits]

/-- `ZMod 2` indicator of a `Bool`: `true ↦ 1`, `false ↦ 0`. -/
private def bId (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma bId_inj (h : bId a = bId b) : a = b := by decide +revert
@[simp] private lemma bId_xor : bId (a ^^ b) = bId a + bId b := by decide +revert
@[simp] private lemma bId_and : bId (a && b) = bId a * bId b := by decide +revert

/-- `popParityK v` is the XOR over the low 32 bits of `v`. -/
theorem popParityK_eq32 : popParityK v = popParity 32 v := by
  rw [popParity_eq_xorBits]
  apply bId_inj
  simp only [popParityK, Nat.land_eq, Nat.beq_eq', Nat.xor_eq, Nat.shiftRight_eq',
    land_one_beq_one, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.reduceAdd, xorBits, List.range,
    List.range.loop, List.foldr_cons, List.foldr_nil, Bool.xor_false, bId_xor]
  grind

/-- Link between the recursive parity and the `Finset.range` sum over 𝔽₂ indicators. -/
theorem popParity_sum (fuel a : ℕ) :
    bId (popParity fuel a) = ∑ j ∈ range fuel, bId (a.testBit j) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    rw [popParity, sum_range_succ', bId_xor, add_comm, ih]
    simp [Nat.testBit_succ]

section
variable {v n : ℕ}

/-- Extra high bits (`≥ n`) are zero when `v < 2 ^ n`, so they drop out of the XOR. -/
theorem popParity_hi_eq (hv : v < 2 ^ n) (hn : n ≤ 32) : popParity 32 v = popParity n v := by
  rw [popParity_eq_xorBits, popParity_eq_xorBits]
  refine xorBits_range_hi (fun j hj ↦ ?_) hn
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

/-- For `v < 2 ^ n` with `n ≤ 32`, `popParityK v` equals `popParity n v`. -/
theorem popParityK_eq (hv : v < 2 ^ n) (hn : n ≤ 32) : popParityK v = popParity n v := by
  rw [popParityK_eq32, popParity_hi_eq hv hn]

end

@[simp, grind =] theorem checkInvRow_cons (b i k m : ℕ) (ms : List ℕ) :
    checkInvRow b i k (m :: ms) =
      ((popParityK (b &&& m)).rec (motive := fun _ ↦ Bool) (i.beq k).not'
        (i.beq k)).and' (checkInvRow b i k.succ ms) := rfl

@[simp, grind =] theorem checkInvGo_cons (M : List ℕ) (i b : ℕ) (bs : List ℕ) :
    checkInvGo M i (b :: bs) = (checkInvRow b i 0 M).and' (checkInvGo M i.succ bs) := rfl

/-- Interpret a `List Nat` of row bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMat (B : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j ↦ if (B.getD i 0).testBit j then 1 else 0

/-- Entry `(i, j)` of `toMat B n`, for a row index in range: bit `j` of row `i` of `B`. -/
theorem toMat_apply {B : List ℕ} {n : ℕ} {i j : Fin n} (h : i.val < B.length) :
    toMat B n i j = if B[i].testBit j then 1 else 0 := by
  rw [toMat, Matrix.of_apply, List.getD_eq_getElem (hn := h), Fin.getElem_fin]

/-- Interpret a `List Nat` of column bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMatCols (M : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) := (toMat M n).transpose

section
variable {n b i i' k k' : ℕ} {B M : List ℕ}

/-- Column correctness for one row: if `checkInvRow` (started at column index `k`) passes, then at
each column `k'` the parity of `bi &&& M[k']` equals the diagonal indicator `i == k + k'`. -/
theorem checkInvRow_true (hn : n ≤ 32) (hM : ∀ m ∈ M, m < 2 ^ n) (hc : checkInvRow b i k M)
    (hk' : k' < M.length) : popParity n (b &&& M[k']) = (i == k + k') := by
  induction M generalizing k k' with
  | nil => simp at hk'
  | cons m ms ih =>
    simp only [checkInvRow_cons, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨h0, hrec⟩ := hc
    cases k' with
    | zero =>
      have hbnd : b &&& m < 2 ^ n := Nat.and_lt_two_pow b (hM m (by simp))
      rw [popParityK_eq (by grind) hn, Bool.rec_eq] at h0
      grind
    | succ k'' =>
      grind

/-- Row correctness: if `checkInvGo` (started at row index `i`) passes, then for each row `i'` and
column `k'` the parity of `B[i'] &&& M[k']` equals the diagonal indicator `i + i' == k'`. -/
theorem checkInvGo_true (hn : n ≤ 32) (hM : ∀ m ∈ M, m < 2 ^ n)
    (hB : ∀ b ∈ B, b < 2 ^ n) (hc : checkInvGo M i B) (hi' : i' < B.length) (hk' : k' < M.length) :
    popParity n (B[i'] &&& M[k']) = (i + i' == k') := by
  induction B generalizing i i' with
  | nil => simp at hi'
  | cons b bs ih =>
    simp only [checkInvGo_cons, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨hrow, hrec⟩ := hc
    cases i' with
    | zero => simpa using checkInvRow_true hn hM hrow hk'
    | succ i'' => grind

/-- `maskBelow n M` is `true` exactly when every mask in `M` fits in `n` bits. -/
@[grind =] theorem maskBelow_iff : maskBelow n M ↔ ∀ x ∈ M, x < 2 ^ n := by
  rw [maskBelow, allList_iff]
  simp [Nat.shiftLeft_eq', Nat.one_shiftLeft]

/-- The four conjuncts of a passing `checkInv`: bounds on `B`, on `M`, `n ≤ 32`, and the core go. -/
theorem checkInv_true_of (h : checkInv n B M) :
    (∀ b ∈ B, b < 2 ^ n) ∧ (∀ m ∈ M, m < 2 ^ n) ∧ n ≤ 32 ∧ checkInvGo M 0 B := by
  grind [checkInv, maskBelow_iff]

/-- If the aggregate check passes, every `(i, k)` parity equals the diagonal indicator `i == k`. -/
theorem checkInv_true {i k : ℕ} (hi : i < B.length) (hk : k < M.length) (h : checkInv n B M) :
    popParity n (B[i] &&& M[k]) = (i == k) := by
  obtain ⟨hB, hM, hn, hgo⟩ := checkInv_true_of h
  simpa using checkInvGo_true hn hM hB hgo hi hk

/-- If the kernel-reducible checker `checkInv n B M` returns `true` (and `B`, `M` have length `n`),
then the matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
theorem checkInv_isUnit (hBlen : B.length = n) (hMlen : M.length = n) (h : checkInv n B M) :
    IsUnit (toMat B n) := by
  have key : toMat B n * toMatCols M n = 1 := by
    ext i k
    simp only [Matrix.mul_apply, toMat, Matrix.of_apply, toMatCols, ← bId.eq_def, ← bId_and,
      ← Nat.testBit_land, Matrix.transpose_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ bId ((B.getD i 0 &&& M.getD k 0).testBit j)) n,
      ← popParity_sum, Matrix.one_apply]
    grind [bId, checkInv_true]
  exact .of_mul_eq_one (toMatCols M n) key

end

end ECCompute.F2Invert
