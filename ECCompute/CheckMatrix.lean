/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.F2Invert
import ECCompute.LambdaCompute

/-!
# Aggregate descent-character matrix check

`checkB` is a single `Bool` that tests every entry of the certificate matrix `matB` against the
computed descent character `lambdaCompute`, and `checkB_true` recovers the individual entry
equalities from `checkB … = true`.  This lets the `hB` obligation of
`ECCompute.rank_ge_of_certificate` be discharged by one aggregate check (closeable by `quickRfl`)
instead of one `rfl` per matrix entry.
-/

namespace ECCompute

/-- One row of the descent-matrix check.  For the row bitmask `b` (bit `j` is the `(i, j)` entry of
`matB`) and the `x`-coordinate `x` of point `i`, fold structurally over the labels, consuming `b`
one bit at a time (`b >>> 1`) so bit `0` of the running mask is the `(i, j)` entry.  No positional
list access: the kernel peels one label at a time. -/
noncomputable def checkBRow (a₂ a₄ a₆ : ℤ) (x : ℚ) : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | b, l :: ls =>
      (b.testBit 0 == lambdaComputeBool a₂ a₄ a₆ l.1 (l.2 : ZMod l.1) x).and'
        (checkBRow a₂ a₄ a₆ x (b >>> 1) ls)

/-- The aggregate descent-matrix check: fold structurally over the rows, pairing each row bitmask of
`matB` with its point in `pt` (in lockstep), and check each row with `checkBRow`.  No `allBelow`
index and no `getD` — the kernel peels one row and one label at a time. -/
noncomputable def checkB (a₂ a₄ a₆ : ℤ) (lab : List (ℕ × ℤ)) : List ℕ → List (ℚ × ℚ) → Bool
  | b :: bs, p :: ps => (checkBRow a₂ a₄ a₆ p.1 b lab).and' (checkB a₂ a₄ a₆ lab bs ps)
  | _, _ => true

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j` on the point. -/
theorem checkBRow_true {a₂ a₄ a₆ : ℤ} {x : ℚ} {lab : List (ℕ × ℤ)} :
    ∀ {b : ℕ}, checkBRow a₂ a₄ a₆ x b lab = true →
      ∀ j, j < lab.length → b.testBit j = lambdaComputeBool a₂ a₄ a₆ (lab.getD j (0, 0)).1
        ((lab.getD j (0, 0)).2 : ZMod (lab.getD j (0, 0)).1) x := by
  induction lab with
  | nil => intro b _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons l ls ih =>
    intro b hb j hj
    simp only [checkBRow, Bool.and'_eq_and, Bool.and_eq_true] at hb
    obtain ⟨h0, hrec⟩ := hb
    cases j with
    | zero => exact beq_iff_eq.mp h0
    | succ j' =>
      have hrec' := ih hrec j' (by simpa using hj)
      rw [Nat.testBit_shiftRight, Nat.add_comm 1 j'] at hrec'
      exact hrec'

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkB_row {a₂ a₄ a₆ : ℤ} {lab : List (ℕ × ℤ)} :
    ∀ {matB : List ℕ} {pt : List (ℚ × ℚ)}, checkB a₂ a₄ a₆ lab matB pt = true →
      ∀ i, i < matB.length → i < pt.length →
        checkBRow a₂ a₄ a₆ (pt.getD i (0, 0)).1 (matB.getD i 0) lab = true := by
  intro matB
  induction matB with
  | nil => intro _ _ i hi _; exact absurd hi (Nat.not_lt_zero i)
  | cons b bs ih =>
    intro pt h i hi hip
    cases pt with
    | nil => exact absurd hip (Nat.not_lt_zero i)
    | cons p ps =>
      simp only [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
      obtain ⟨hrow, hrec⟩ := h
      cases i with
      | zero => exact hrow
      | succ i' => exact ih hrec i' (by simpa using hi) (by simpa using hip)

/-- If the aggregate check passes, every matrix entry equals the computed descent character.  The
`Bool` equality of `checkB` is read back into `ZMod 2` through `lambdaCompute_eq_bool`.  The point
and label families are read from the lists by `List.getD`, so the kernel never applies a
`Fin rho → _` function. -/
theorem checkB_true {a₂ a₄ a₆ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {pt : List (ℚ × ℚ)}
    (hBlen : matB.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (h : checkB a₂ a₄ a₆ lab matB pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ a₆ (lab.getD j.val (0, 0)).1
        ((lab.getD j.val (0, 0)).2 : ZMod (lab.getD j.val (0, 0)).1) (pt.getD i.val (0, 0)).1 := by
  intro i j
  have hi : i.val < matB.length := by rw [hBlen]; exact i.isLt
  have hip : i.val < pt.length := by rw [hplen]; exact i.isLt
  have hj : j.val < lab.length := by rw [hllen]; exact j.isLt
  have hcell := checkBRow_true (checkB_row h i.val hi hip) j.val hj
  rw [lambdaCompute_eq_bool]
  simp only [F2Invert.toMat]
  rw [hcell]

end ECCompute
