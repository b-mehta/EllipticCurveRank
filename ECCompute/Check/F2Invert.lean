/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Range
import ECCompute.Check.Fold

/-!
# Kernel-reducible 𝔽₂ matrix invertibility certificates

We certify that a square matrix `B` over `𝔽₂ = ZMod 2` is invertible by supplying a claimed
inverse `M` and checking `B * M = I` with a kernel-reducible `Bool` function.

## Representation

An `n × n` matrix over `𝔽₂` is given as a `List Nat` of length `n`, one `Nat` bitmask per line,
where bit `j` of the `i`-th entry is the `(i, j)` matrix entry.

* `B` is supplied by rows: bit `j` of `B.getD i 0` is `B i j`.
* `M` is supplied by columns: bit `j` of `M.getD k 0` is `M j k`.

With this layout the `(i, k)` entry of `B * M` is the parity of the popcount of
`B.getD i 0 &&& M.getD k 0`.

## Main results

* `checkInv` : the `Bool` certificate checker.
* `checkInv_isUnit` : the correctness lemma, `checkInv n B M = true → IsUnit (toMat B n)`.
-/

namespace ECCompute.F2Invert

open Matrix Finset

/-- Parity of the popcount of `a`, reading the low `fuel` bits. -/
def popParity : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, a => Bool.xor (a.testBit 0) (popParity fuel (a / 2))

/-- Kernel-reducible variant of `popParity`, phrased with `Nat.rec` and `Bool.rec` so the kernel
peels the low bit and flips the running result. Equal to `popParity` (see
`popParityK_eq_popParity`). -/
noncomputable def popParityK : Nat → Nat → Bool :=
  Nat.rec (fun _ ↦ false)
    fun _ r a ↦ ((a.land 1).beq 0).rec (r (a.div 2)).not' (r (a.div 2))

/-- `popParityK` computes the same bit-parity as `popParity`. -/
theorem popParityK_eq_popParity (fuel a : Nat) : popParityK fuel a = popParity fuel a := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    change ((a.land 1).beq 0).rec (popParityK f (a.div 2)).not' (popParityK f (a.div 2))
        = Bool.xor (a.testBit 0) (popParity f (a / 2))
    have hdiv : a.div 2 = a / 2 := rfl
    have hland : a.land 1 = a % 2 := Nat.and_one_is_mod a
    rw [ih, Bool.not'_eq_not, Nat.testBit_zero, hdiv, hland]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;>
      cases popParity f (a / 2) <;> rfl

/-- One row's contribution to the inverse check: for the row bitmask `bi` at row index `i`, fold
over the columns of `M`, comparing the parity of `bi &&& mₖ` against the diagonal indicator
`i == k`. -/
noncomputable def checkInvRow (bi i n : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | k, m :: ms => (popParityK n (bi &&& m) == (i == k)).and' (checkInvRow bi i n (k + 1) ms)

/-- Fold over the rows of `B`, checking each against the columns of `M` with `checkInvRow`. -/
noncomputable def checkInvGo (n : Nat) (M : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, b :: bs => (checkInvRow b i n 0 M).and' (checkInvGo n M (i + 1) bs)

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  checkInvGo n M 0 B

/-- Interpret a `List Nat` of row bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMat (B : List Nat) (n : Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (B.getD i 0).testBit j then 1 else 0

/-- Interpret a `List Nat` of column bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMatCols (M : List Nat) (n : Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun j k => if (M.getD k 0).testBit j then 1 else 0

/-- Product of two 𝔽₂ indicator bits is the indicator of the bit of the `Nat.land`. -/
private theorem prodTerm (a b j : Nat) :
    (if a.testBit j then (1 : ZMod 2) else 0) * (if b.testBit j then 1 else 0)
      = if (a &&& b).testBit j then 1 else 0 := by grind

/-- `Bool.xor` corresponds to addition of 𝔽₂ indicators. -/
private theorem xor_add (p q : Bool) :
    (if Bool.xor p q then (1 : ZMod 2) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  cases p <;> cases q <;> decide

/-- Link between the recursive parity and the `Finset.range` sum over 𝔽₂ indicators. -/
theorem popParity_sum (fuel a : Nat) :
    (if popParity fuel a then (1 : ZMod 2) else 0)
      = ∑ j ∈ Finset.range fuel, (if a.testBit j then (1 : ZMod 2) else 0) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    rw [popParity, Finset.sum_range_succ', xor_add, add_comm, ih]
    simp [Nat.testBit_succ]

/-- Column correctness for one row: if `checkInvRow` (started at column index `k`) passes, then at
each column `k'` the parity of `bi &&& M[k']` equals the diagonal indicator `i == k + k'`. -/
theorem checkInvRow_true {bi i n : Nat} :
    ∀ {k : Nat} {M : List Nat}, checkInvRow bi i n k M = true →
      ∀ k', k' < M.length → (popParityK n (bi &&& M.getD k' 0) == (i == (k + k'))) = true := by
  intro k M
  induction M generalizing k with
  | nil => intro _ k' hk'; simp at hk'
  | cons m ms ih =>
    intro hc k' hk'
    simp only [checkInvRow, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨h0, hrec⟩ := hc
    cases k' with
    | zero => simpa using h0
    | succ k'' =>
      have hidx : k + (k'' + 1) = k + 1 + k'' := by lia
      rw [hidx]
      exact ih hrec k'' (by simpa using hk')

/-- Row correctness: if `checkInvGo` (started at row index `i`) passes, then for each row `i'` and
column `k'` the parity of `B[i'] &&& M[k']` equals the diagonal indicator `i + i' == k'`. -/
theorem checkInvGo_true {n : Nat} {M : List Nat} :
    ∀ {i : Nat} {B : List Nat}, checkInvGo n M i B = true →
      ∀ i', i' < B.length → ∀ k', k' < M.length →
        (popParityK n (B.getD i' 0 &&& M.getD k' 0) == (i + i' == k')) = true := by
  intro i B
  induction B generalizing i with
  | nil => intro _ i' hi'; simp at hi'
  | cons b bs ih =>
    intro hc i' hi' k' hk'
    simp only [checkInvGo, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨hrow, hrec⟩ := hc
    cases i' with
    | zero => simpa using checkInvRow_true hrow k' hk'
    | succ i'' =>
      have hidx : i + (i'' + 1) = i + 1 + i'' := by lia
      rw [hidx]
      exact ih hrec i'' (by simpa using hi') k' hk'

/-- If the aggregate check passes, every `(i, k)` parity equals the diagonal indicator `i == k`. -/
theorem checkInv_true {n : Nat} {B M : List Nat} (h : checkInv n B M = true) :
    ∀ i k, i < B.length → k < M.length →
      (popParityK n (B.getD i 0 &&& M.getD k 0) == (i == k)) = true := by
  intro i k hi hk
  simpa using checkInvGo_true (n := n) (M := M) (i := 0) (B := B) h i hi k hk

/-- If the kernel-reducible checker `checkInv n B M` returns `true` (and `B`, `M` have length `n`),
then the matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
theorem checkInv_isUnit (n : Nat) (B M : List Nat) (hBlen : B.length = n) (hMlen : M.length = n)
    (h : checkInv n B M = true) : IsUnit (toMat B n) := by
  -- First: `B * M = 1` as matrices over `ZMod 2`.
  have key : toMat B n * toMatCols M n = 1 := by
    ext i k
    -- Turn the product-of-indicators sum into a single indicator sum, then use `popParity_sum`.
    simp only [Matrix.mul_apply, toMat, toMatCols, prodTerm]
    rw [Fin.sum_univ_eq_sum_range
        (fun j => if (B.getD i 0 &&& M.getD k 0).testBit j then (1 : ZMod 2) else 0) n,
      ← popParity_sum, Matrix.one_apply]
    -- Read off the `(i, k)` certificate; `grind` matches it against the diagonal.
    have hb := checkInv_true h i.val k.val
      (by rw [hBlen]; exact i.isLt) (by rw [hMlen]; exact k.isLt)
    rw [popParityK_eq_popParity] at hb
    grind
  -- Square matrices over a finite (hence Dedekind-finite) monoid: a right inverse is a unit.
  exact IsUnit.of_mul_eq_one (toMatCols M n) key

/-! ## Worked 3×3 example

`B = [[1,1,0],[0,1,1],[0,0,1]]` with inverse `M = [[1,1,1],[0,1,1],[0,0,1]]` over `𝔽₂`.
Rows of `B` as bitmasks (bit `j` = column `j`): `[3, 6, 4]`.
Columns of `M` as bitmasks (bit `j` = row `j`): `[1, 3, 7]`. -/

/-- The certificate reduces to `true` in the kernel by `rfl`. -/
example : checkInv 3 [3, 6, 4] [1, 3, 7] = true := rfl

/-- Hence the interpreted matrix is invertible over `𝔽₂`, end-to-end from the `rfl` certificate. -/
example : IsUnit (toMat [3, 6, 4] 3) :=
  checkInv_isUnit 3 [3, 6, 4] [1, 3, 7] rfl rfl rfl

end ECCompute.F2Invert
