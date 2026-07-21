/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Check.F2Invert
import ECCompute.Theory.LambdaCompute

/-!
# Aggregate descent-character matrix check

`checkB` is a single `Bool` that tests every entry of the certificate matrix `matB` against the
computed descent character `lambdaCompute`; `checkB_true` recovers the individual entry equalities
from `checkB … = true`.
-/

namespace ECCompute

/-- One row of the descent-matrix check: for the row bitmask `b` and the `x`-coordinate of point
`i`, fold over the labels, consuming `b` one bit at a time (`b >>> 1`). -/
noncomputable def checkBRow (a₂ a₄ a₆ : ℤ) (x : ℚ) : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | b, l :: ls =>
      (b.testBit 0 == lambdaComputeBool a₂ a₄ a₆ l.1 (l.2 : ZMod l.1) x).and'
        (checkBRow a₂ a₄ a₆ x (b >>> 1) ls)

/-- The aggregate descent-matrix check: fold over the rows, pairing each row bitmask of `matB` with
its point in `pt`, and check each row with `checkBRow`. -/
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
  | nil => grind
  | cons l ls ih =>
    intro b hb j hj
    simp only [checkBRow, Bool.and'_eq_and, Bool.and_eq_true] at hb
    cases j <;> grind

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkB_row {a₂ a₄ a₆ : ℤ} {lab : List (ℕ × ℤ)} :
    ∀ {matB : List ℕ} {pt : List (ℚ × ℚ)}, checkB a₂ a₄ a₆ lab matB pt = true →
      ∀ i, i < matB.length → i < pt.length →
        checkBRow a₂ a₄ a₆ (pt.getD i (0, 0)).1 (matB.getD i 0) lab = true := by
  intro matB
  induction matB with
  | nil => grind
  | cons b bs ih =>
    intro pt h i hi hip
    cases pt with
    | nil => grind
    | cons p ps =>
      simp only [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
      cases i <;> grind

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {a₂ a₄ a₆ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {pt : List (ℚ × ℚ)}
    (hBlen : matB.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (h : checkB a₂ a₄ a₆ lab matB pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ a₆ (lab.getD j.val (0, 0)).1
        ((lab.getD j.val (0, 0)).2 : ZMod (lab.getD j.val (0, 0)).1) (pt.getD i.val (0, 0)).1 := by
  intro i j
  have hcell := checkBRow_true (checkB_row h i.val (hBlen ▸ i.isLt) (hplen ▸ i.isLt))
    j.val (hllen ▸ j.isLt)
  grind [lambdaCompute_eq_bool, F2Invert.toMat]

end ECCompute
