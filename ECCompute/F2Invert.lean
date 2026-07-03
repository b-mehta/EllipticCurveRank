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

/-- Kernel-reducible variant of `popParity`, phrased directly with `Nat.rec` and `Bool.rec`
so the kernel peels the low bit (`a.land 1`, `a.div 2`) and flips the running result with
`Bool.not'` when the low bit is set. Equal to `popParity` (see `popParityK_eq_popParity`);
`noncomputable` only because `Bool.not'` is, which the kernel reduces regardless. -/
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
    rw [ih, Bool.not'_eq_not, Nat.testBit_zero, show a.div 2 = a / 2 from rfl,
      show a.land 1 = a % 2 from Nat.and_one_is_mod a]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;>
      cases popParity f (a / 2) <;> rfl

/-- Kernel-reducible bounded `∀`: `true` iff `p m = true` for every `m < n`. Phrased directly
with `Nat.rec` (folding with the primed `Bool.and'`) so the kernel peels one `m` at a time,
which reduces far better than `(List.range n).all p`. `noncomputable` only because `Bool.and'`
is; the kernel reduces it regardless. -/
noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun m r => (p m).and' r) n

/-- Kernel-reducible bounded `∃`: `true` iff `p m = true` for some `m < n`, the `Bool.or'` fold
dual to `allBelow`. -/
noncomputable def anyBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec false (fun m r => (p m).or' r) n

/-- `allBelow (n + 1) p` peels the top index: it folds `p n` into `allBelow n p`. -/
theorem allBelow_succ (n : Nat) (p : Nat → Bool) :
    allBelow (n + 1) p = (p n).and' (allBelow n p) := rfl

/-- `anyBelow (n + 1) p` peels the top index: it folds `p n` into `anyBelow n p`. -/
theorem anyBelow_succ (n : Nat) (p : Nat → Bool) :
    anyBelow (n + 1) p = (p n).or' (anyBelow n p) := rfl

/-- `allBelow` computes the bounded universal quantifier over `m < n`. -/
theorem allBelow_eq_true {n : Nat} {p : Nat → Bool} :
    allBelow n p = true ↔ ∀ m, m < n → p m = true := by
  induction n with
  | zero => simp [allBelow]
  | succ k ih =>
    rw [allBelow_succ, Bool.and'_eq_and, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hk, hlt⟩ m hm
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hm) with h | h
      · exact hlt m h
      · exact h ▸ hk
    · exact fun h => ⟨h k (Nat.lt_succ_self k), fun m hm => h m (Nat.lt_succ_of_lt hm)⟩

/-- `anyBelow` is `false` exactly when `p` fails at every `m < n`. -/
theorem anyBelow_eq_false {n : Nat} {p : Nat → Bool} :
    anyBelow n p = false ↔ ∀ m, m < n → p m = false := by
  induction n with
  | zero => simp [anyBelow]
  | succ k ih =>
    rw [anyBelow_succ, Bool.or'_eq_or, Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨hk, hlt⟩ m hm
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hm) with h | h
      · exact hlt m h
      · exact h ▸ hk
    · exact fun h => ⟨h k (Nat.lt_succ_self k), fun m hm => h m (Nat.lt_succ_of_lt hm)⟩

/-- Kernel-reducible certificate checker: `true` iff `B * M = I` over `𝔽₂`, where `B` is
given by rows and `M` by columns (each a `Nat` bitmask), and `n` is the dimension.
`noncomputable` because it calls `popParityK`; the kernel reduces it regardless (via `rfl`). -/
noncomputable def checkInv (n : Nat) (B M : List Nat) : Bool :=
  allBelow n fun i =>
    allBelow n fun k =>
      popParityK n (B.getD i 0 &&& M.getD k 0) == (i == k)

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

/-- Bridge between the recursive parity and the `Finset.range` sum over 𝔽₂ indicators. -/
theorem popParity_sum (fuel a : Nat) :
    (if popParity fuel a then (1 : ZMod 2) else 0)
      = ∑ j ∈ Finset.range fuel, (if a.testBit j then (1 : ZMod 2) else 0) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ f ih =>
    rw [popParity, Finset.sum_range_succ', xor_add, add_comm, ih]
    simp [Nat.testBit_succ]

/-- **Bridge lemma.** If the kernel-reducible checker `checkInv n B M` returns `true`, then the
matrix `toMat B n` interpreted over `𝔽₂` is invertible (a unit). -/
theorem checkInv_isUnit (n : Nat) (B M : List Nat) (h : checkInv n B M = true) :
    IsUnit (toMat B n) := by
  -- First: `B * M = 1` as matrices over `ZMod 2`.
  have key : toMat B n * toMatCols M n = 1 := by
    ext i k
    -- Turn the product-of-indicators sum into a single indicator sum, then use `popParity_sum`.
    simp only [Matrix.mul_apply, toMat, toMatCols, prodTerm]
    rw [Fin.sum_univ_eq_sum_range
        (fun j => if (B.getD i 0 &&& M.getD k 0).testBit j then (1 : ZMod 2) else 0) n,
      ← popParity_sum, Matrix.one_apply]
    -- Unfold the checker to its pointwise form; `grind` reads off the `(i, k)` certificate.
    simp only [checkInv, popParityK_eq_popParity, allBelow_eq_true] at h
    grind
  -- Square matrices over a finite (hence Dedekind-finite) monoid: a right inverse is a unit.
  exact ⟨⟨toMat B n, toMatCols M n, key, mul_eq_one_comm.mp key⟩, rfl⟩

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
