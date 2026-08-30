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
import Mathlib.Data.List.Range
import ECCompute.ForLean

/-!
# Soundness of the kernel-reducible 𝔽₂ matrix invertibility certificate

Correctness proofs for the `Bool` checker `ECCompute.F2Invert.checkInv` (defined in
`ECCompute.Kernel`): supplying a claimed inverse `M` (by rows) and checking `B * M = I` certifies
that the square matrix over `𝔽₂ = ZMod 2` interpreted from `B` is invertible.

MEASUREMENT-ONLY BRANCH: the checker now computes `B * M = I` as an xor-of-selected-rows fold
(`invRowK`) with `M` supplied by rows. The proofs below are stated against the new shape and left as
`sorry`; this branch exists to time the kernel check, not to re-establish soundness.

## Main results

* `checkInv_isUnit` : `checkInv n B M → IsUnit (toMat B n)`, the invertibility certificate.
-/

namespace ECCompute.F2Invert

open Finset

variable {v : ℕ} {a b : Bool}

/-- `ZMod 2` indicator of a `Bool`: `true ↦ 1`, `false ↦ 0`. -/
def bId (b : Bool) : ZMod 2 := if b then 1 else 0

lemma bId_inj (h : bId a = bId b) : a = b := by decide +revert +kernel
@[simp] lemma bId_xor : bId (a ^^ b) = bId a + bId b := by decide +revert +kernel
@[simp] lemma bId_and : bId (a && b) = bId a * bId b := by decide +revert +kernel

@[simp, grind =] theorem checkInvGo_cons {Mr : List ℕ} {i b : ℕ} {bs : List ℕ} :
    checkInvGo Mr i (b :: bs) = (invRowK i b Mr).and' (checkInvGo Mr i.succ bs) := rfl

/-- Interpret a `List Nat` of row bitmasks as an `n × n` matrix over `𝔽₂`. -/
public def toMat (B : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j ↦ if (B.getD i 0).testBit j then 1 else 0

/-- Entry `(i, j)` of `toMat B n`, for a row index in range: bit `j` of row `i` of `B`. -/
public theorem toMat_apply {B : List ℕ} {n : ℕ} {i j : Fin n} (h : i.val < B.length) :
    toMat B n i j = if B[i].testBit j then 1 else 0 := by
  rw [toMat, Matrix.of_apply, List.getD_eq_getElem _ _ h, Fin.getElem_fin]

section
variable {n b i i' : ℕ} {B M : List ℕ}

/-- `maskBelow n M` is `true` exactly when every mask in `M` fits in `n` bits. -/
@[grind =] theorem maskBelow_iff : maskBelow n M ↔ ∀ x ∈ M, x < 2 ^ n := by
  rw [maskBelow, allList_iff]
  simp [Nat.shiftLeft_eq', Nat.one_shiftLeft]

/-- If the aggregate check `checkInv n B M` passes then, over `𝔽₂`, the xor of the rows of `M`
selected by the set bits of `B[i]` is the unit vector `1 <<< i`. (Measurement branch: proof
deferred.) -/
theorem checkInv_true (hi : i < B.length) (h : checkInv n B M) :
    invRowK i B[i] M := by sorry

/-- If the kernel-reducible checker `checkInv n B M` returns `true` (and `B`, `M` have length `n`),
then the matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). (Measurement branch:
proof deferred.) -/
public theorem checkInv_isUnit (hBlen : B.length = n) (hMlen : M.length = n) (h : checkInv n B M) :
    IsUnit (toMat B n) := by sorry

end

end ECCompute.F2Invert
