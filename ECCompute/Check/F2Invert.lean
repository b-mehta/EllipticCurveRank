/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

/-- XOR of the low 32 bits of `v`, folded into bit 0 by five shift-xor stages (16, 8, 4, 2, 1).
For input `v < 2 ^ n` this equals the spec `popParity n v` (`popParityK_eq`), the range `checkInv`
enforces through `maskBelow`. -/
noncomputable def popParityK (v : Nat) : Bool :=
  let v := v.xor (v.shiftRight 16); let v := v.xor (v.shiftRight 8)
  let v := v.xor (v.shiftRight 4); let v := v.xor (v.shiftRight 2)
  let v := v.xor (v.shiftRight 1)
  (v.land 1).beq 1

/-- `(x.land 1).beq 1` reads bit 0 of `x`. -/
private theorem land_one_beq_one (x : Nat) : (x.land 1).beq 1 = x.testBit 0 := by
  have hl : x.land 1 = x &&& 1 := rfl
  rw [Nat.testBit_zero, hl, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl

/-- The XOR over `v.testBit j` for `j` in a list. -/
private def xorBits (v : Nat) (l : List Nat) : Bool :=
  l.foldr (fun j r => Bool.xor (v.testBit j) r) false

/-- `popParity fuel a` is the XOR over the low `fuel` bits of `a` (indices `0 … fuel-1`). -/
theorem popParity_eq_xorBits (fuel a : Nat) :
    popParity fuel a = xorBits a (List.range fuel) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    rw [popParity, ih, List.range_succ_eq_map]
    simp only [xorBits, List.foldr_cons, List.foldr_map, Nat.testBit_zero, Nat.testBit_succ]

/-- `ZMod 2` image of a `Bool`; injective and turns `Bool.xor` into `+`. -/
private def bId (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bId_inj {a b : Bool} (h : bId a = bId b) : a = b := by
  cases a <;> cases b <;> simp_all [bId]

private theorem bId_xor (a b : Bool) : bId (Bool.xor a b) = bId a + bId b := by
  cases a <;> cases b <;> decide

/-- Unconditional: bit 0 of the five-stage fold is the XOR over the low 32 bits. -/
theorem popParityK_eq32 (v : Nat) : popParityK v = popParity 32 v := by
  rw [popParity_eq_xorBits]
  apply bId_inj
  have hxor : ∀ a b : Nat, a.xor b = a ^^^ b := fun _ _ => rfl
  have hshr : ∀ a b : Nat, a.shiftRight b = a >>> b := fun _ _ => rfl
  simp only [popParityK, land_one_beq_one, hxor, hshr, Nat.testBit_xor,
    Nat.testBit_shiftRight]
  simp only [xorBits, List.range, List.range.loop, List.foldr_cons, List.foldr_nil]
  -- both sides are explicit XOR trees over `v.testBit c`; push into `ZMod 2` and `ring`
  simp only [Bool.xor_false, bId_xor]
  ring

/-- Dropping trailing indices whose bit is `false` does not change the XOR. -/
private theorem xorBits_range_hi {v n : Nat} (hzero : ∀ j, n ≤ j → v.testBit j = false) :
    ∀ m, n ≤ m → xorBits v (List.range m) = xorBits v (List.range n) := by
  intro m
  induction m with
  | zero => intro h; rw [Nat.le_zero.1 h]
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · rw [List.range_succ]
      simp only [xorBits, List.foldr_append, List.foldr_cons, List.foldr_nil,
        hzero k (by omega), Bool.xor_false]
      exact ih (by omega)
    · have : k + 1 = n := by omega
      rw [this]

/-- Extra high bits (`≥ n`) are zero when `v < 2 ^ n`, so they drop out of the XOR. -/
theorem popParity_hi_eq {v n : Nat} (hv : v < 2 ^ n) (hn : n ≤ 32) :
    popParity 32 v = popParity n v := by
  rw [popParity_eq_xorBits, popParity_eq_xorBits]
  refine xorBits_range_hi (fun j hj => ?_) 32 hn
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

/-- Bridge: for `v < 2 ^ n` with `n ≤ 32`, the fold matches the `n`-bit `popParityK`. -/
theorem popParityK_eq {v n : Nat} (hv : v < 2 ^ n) (hn : n ≤ 32) :
    popParityK v = popParity n v := by
  rw [popParityK_eq32, popParity_hi_eq hv hn]

/-- One row's contribution to the inverse check: for the row bitmask `bi` at row index `i`, fold
over the columns of `M`, comparing the parity of `bi &&& mₖ` (via `popParityK`)
against the diagonal indicator `i == k`. Soundness of the fold requires `bi, mₖ < 2 ^ n` with
`n ≤ 32`, which `checkInv` verifies separately. -/
noncomputable def checkInvRow (bi i k : Nat) (M : List Nat) : Bool :=
  M.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih k => ((popParityK (Nat.land bi m)).rec (motive := fun _ => Bool)
      (Nat.beq i k).not' (Nat.beq i k)).and' (ih k.succ)) k

theorem checkInvRow_cons (bi i k m : Nat) (ms : List Nat) :
    checkInvRow bi i k (m :: ms) =
      ((popParityK (Nat.land bi m)).rec (motive := fun _ => Bool) (Nat.beq i k).not'
        (Nat.beq i k)).and' (checkInvRow bi i k.succ ms) := rfl

/-- Fold over the rows of `B`, checking each against the columns of `M` with `checkInvRow`. -/
noncomputable def checkInvGo (M : List Nat) (i : Nat) (B : List Nat) : Bool :=
  B.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih i => (checkInvRow b i 0 M).and' (ih i.succ)) i

theorem checkInvGo_cons (M : List Nat) (i b : Nat) (bs : List Nat) :
    checkInvGo M i (b :: bs) =
      (checkInvRow b i 0 M).and' (checkInvGo M i.succ bs) := rfl

/-- Every mask in `L` fits in `n` bits (`< 2 ^ n`). -/
noncomputable def maskBelow (n : Nat) (L : List Nat) : Bool :=
  allList (fun x => Nat.blt x (Nat.shiftLeft 1 n)) L

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is given by
rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension. Also verifies that all
masks fit in `n ≤ 32` bits, which `popParityK` relies on for soundness. -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  (maskBelow n B).and' ((maskBelow n M).and' ((Nat.ble n 32).and' (checkInvGo M 0 B)))

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
theorem checkInvRow_true {bi i n : Nat} (hn : n ≤ 32) :
    ∀ {k : Nat} {M : List Nat}, (∀ m ∈ M, m < 2 ^ n) → checkInvRow bi i k M = true →
      ∀ k', k' < M.length → (popParity n (bi &&& M.getD k' 0) == (i == (k + k'))) = true := by
  intro k M
  induction M generalizing k with
  | nil => intro _ _ k' hk'; simp at hk'
  | cons m ms ih =>
    intro hM hc k' hk'
    simp only [checkInvRow_cons, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨h0, hrec⟩ := hc
    cases k' with
    | zero =>
      have hbnd : bi &&& m < 2 ^ n := Nat.and_lt_two_pow bi (hM m (by simp))
      have hlm : bi.land m = bi &&& m := rfl
      rw [hlm, popParityK_eq hbnd hn] at h0
      have hbe := (by decide : ∀ x y : Bool, (x.rec y.not' y = true) → x = y) _ _ h0
      simpa [← natBeqEq, beq_iff_eq] using hbe
    | succ k'' =>
      have hidx : k + (k'' + 1) = k + 1 + k'' := by lia
      rw [hidx]
      exact ih (fun m hm => hM m (by simp [hm])) hrec k'' (by simpa using hk')

/-- Row correctness: if `checkInvGo` (started at row index `i`) passes, then for each row `i'` and
column `k'` the parity of `B[i'] &&& M[k']` equals the diagonal indicator `i + i' == k'`. -/
theorem checkInvGo_true {n : Nat} {M : List Nat} (hn : n ≤ 32) (hM : ∀ m ∈ M, m < 2 ^ n) :
    ∀ {i : Nat} {B : List Nat}, (∀ b ∈ B, b < 2 ^ n) → checkInvGo M i B = true →
      ∀ i', i' < B.length → ∀ k', k' < M.length →
        (popParity n (B.getD i' 0 &&& M.getD k' 0) == (i + i' == k')) = true := by
  intro i B
  induction B generalizing i with
  | nil => intro _ _ i' hi'; simp at hi'
  | cons b bs ih =>
    intro hB hc i' hi' k' hk'
    simp only [checkInvGo_cons, Bool.and'_eq_and, Bool.and_eq_true] at hc
    obtain ⟨hrow, hrec⟩ := hc
    cases i' with
    | zero => simpa using checkInvRow_true hn hM hrow k' hk'
    | succ i'' =>
      have hidx : i + (i'' + 1) = i + 1 + i'' := by lia
      rw [hidx]
      exact ih (fun b hb => hB b (by simp [hb])) hrec i'' (by simpa using hi') k' hk'

/-- `Nat.shiftLeft 1 n` is `2 ^ n`, restated in the def's primitive `Nat.shiftLeft` form. -/
private theorem shiftLeft_one (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

/-- `maskBelow n L` is `true` exactly when every mask in `L` fits in `n` bits. -/
theorem maskBelow_eq_true {n : Nat} {L : List Nat} :
    maskBelow n L = true ↔ ∀ x ∈ L, x < 2 ^ n := by
  rw [maskBelow, allList_eq_true]
  simp only [shiftLeft_one, Nat.blt_eq]

/-- The four conjuncts of a passing `checkInv`: bounds on `B`, on `M`, `n ≤ 32`, and the core go. -/
theorem checkInv_true_of {n : Nat} {B M : List Nat} (h : checkInv n B M = true) :
    (∀ b ∈ B, b < 2 ^ n) ∧ (∀ m ∈ M, m < 2 ^ n) ∧ n ≤ 32 ∧ checkInvGo M 0 B = true := by
  simp only [checkInv, Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hB, hMask, hle, hgo⟩ := h
  exact ⟨maskBelow_eq_true.1 hB, maskBelow_eq_true.1 hMask, by simpa using hle, hgo⟩

/-- If the aggregate check passes, every `(i, k)` parity equals the diagonal indicator `i == k`. -/
theorem checkInv_true {n : Nat} {B M : List Nat} (h : checkInv n B M = true) :
    ∀ i k, i < B.length → k < M.length →
      (popParity n (B.getD i 0 &&& M.getD k 0) == (i == k)) = true := by
  intro i k hi hk
  obtain ⟨hB, hM, hn, hgo⟩ := checkInv_true_of h
  have hgo := checkInvGo_true (n := n) (M := M) hn hM (i := 0) (B := B) hB hgo i hi k hk
  simpa using hgo

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
