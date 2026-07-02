/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Range

/-!
# Kernel-reducible 𝔽₂ matrix invertibility certificates

We certify that a square matrix `B` over `𝔽₂ = ZMod 2` is invertible by *supplying*
a claimed inverse `M` and checking `B * M = I` with a kernel-reducible `Bool` function.

## Representation

An `n × n` matrix over `𝔽₂` is given as a `List Nat` of length `n`, one `Nat` bitmask
per line, where bit `j` of the `i`-th entry is the `(i, j)` matrix entry.

* `B` is supplied **by rows**: bit `j` of `B.getD i 0` is `B i j`.
* `M` is supplied **by columns**: bit `j` of `M.getD k 0` is `M j k`.

With this layout the `(i, k)` entry of `B * M` over `𝔽₂` is the parity of the popcount of
`B.getD i 0 &&& M.getD k 0`, computed with the kernel's GMP-backed `Nat.testBit` / `/ 2`
and `Bool.xor` — no `Finset.sum`, no `Decidable.decide`.

## Main results

* `checkInv` : the `Bool` certificate checker.
* `checkInv_isUnit` : the bridge lemma, `checkInv n B M = true → IsUnit (toMat B n)`.
-/

namespace ECCompute.F2Invert

open Matrix Finset

/-- Parity of the popcount of `a`, reading the low `fuel` bits. Structurally recursive on
`fuel` so the kernel reduces it via `Nat.rec`, using GMP-backed `Nat.testBit` and `/ 2`. -/
def popParity : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, a => Bool.xor (a.testBit 0) (popParity fuel (a / 2))

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is
given by rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. -/
def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range n).all fun k =>
      popParity n (B.getD i 0 &&& M.getD k 0) == (i == k)

/-- Interpret a `List Nat` of row bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMat (B : List Nat) (n : Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (B.getD i 0).testBit j then 1 else 0

/-- Interpret a `List Nat` of column bitmasks as an `n × n` matrix over `𝔽₂`. -/
def toMatCols (M : List Nat) (n : Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun j k => if (M.getD k 0).testBit j then 1 else 0

/-- Product of two 𝔽₂ indicator bits is the indicator of the bit of the `Nat.land`. -/
private theorem prodTerm (a b j : Nat) :
    (if a.testBit j then (1 : ZMod 2) else 0) * (if b.testBit j then 1 else 0)
      = if (a &&& b).testBit j then 1 else 0 := by
  rw [Nat.testBit_and]
  cases a.testBit j <;> cases b.testBit j <;> simp

/-- `Bool.xor` corresponds to addition of 𝔽₂ indicators. -/
private theorem xor_add (p q : Bool) :
    (if Bool.xor p q then (1 : ZMod 2) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  cases p <;> cases q <;> decide

/-- Bridge between the recursive parity and the `Finset.range` sum over 𝔽₂ indicators. -/
theorem popParity_sum (fuel a : Nat) :
    (if popParity fuel a then (1 : ZMod 2) else 0)
      = ∑ j ∈ Finset.range fuel, (if a.testBit j then (1 : ZMod 2) else 0) := by
  induction fuel generalizing a with
  | zero => simp [popParity]
  | succ f ih =>
    rw [popParity, Finset.sum_range_succ', xor_add, add_comm]
    congr 1
    rw [ih]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.testBit_succ]

/-- **Bridge lemma.** If the kernel-reducible checker `checkInv n B M` returns `true`, then the
matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
theorem checkInv_isUnit (n : Nat) (B M : List Nat) (h : checkInv n B M = true) :
    IsUnit (toMat B n) := by
  -- First: `B * M = 1` as matrices over `ZMod 2`.
  have key : toMat B n * toMatCols M n = 1 := by
    ext i k
    rw [Matrix.mul_apply]
    -- Turn the product-of-indicators sum into a single indicator sum, then use `popParity_sum`.
    simp only [toMat, toMatCols, prodTerm]
    rw [Fin.sum_univ_eq_sum_range
        (fun j => if (B.getD i 0 &&& M.getD k 0).testBit j then (1 : ZMod 2) else 0) n,
      ← popParity_sum, Matrix.one_apply]
    -- Extract the pointwise certificate equation from `h`.
    unfold checkInv at h
    rw [List.all_eq_true] at h
    have hi := h i (List.mem_range.mpr i.isLt)
    rw [List.all_eq_true] at hi
    have hik := hi k (List.mem_range.mpr k.isLt)
    have hEq : popParity n (B.getD i 0 &&& M.getD k 0) = ((i : Nat) == (k : Nat)) :=
      beq_iff_eq.mp hik
    rw [hEq]
    by_cases hik' : i = k
    · simp [hik']
    · have hne : (i : Nat) ≠ (k : Nat) := fun hc => hik' (Fin.ext hc)
      simp [beq_eq_false_iff_ne.mpr hne, hik']
  -- Square matrices over a finite (hence Dedekind-finite) monoid: a right inverse is a unit.
  have hcomm : toMatCols M n * toMat B n = 1 := mul_eq_one_comm.mp key
  exact ⟨⟨toMat B n, toMatCols M n, key, hcomm⟩, rfl⟩

/-! ## Worked 3×3 example

`B = [[1,1,0],[0,1,1],[0,0,1]]` with inverse `M = [[1,1,1],[0,1,1],[0,0,1]]` over `𝔽₂`.
Rows of `B` as bitmasks (bit `j` = column `j`): `[3, 6, 4]`.
Columns of `M` as bitmasks (bit `j` = row `j`): `[1, 3, 7]`. -/

/-- The certificate reduces to `true` in the kernel by `rfl`. -/
example : checkInv 3 [3, 6, 4] [1, 3, 7] = true := rfl

/-- Hence the interpreted matrix is invertible over `𝔽₂`, end-to-end from the `rfl` certificate. -/
example : IsUnit (toMat [3, 6, 4] 3) :=
  checkInv_isUnit 3 [3, 6, 4] [1, 3, 7] rfl

end ECCompute.F2Invert
