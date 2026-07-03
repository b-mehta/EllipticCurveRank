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

/-- `true` iff every entry of `matB` equals the computed descent character `λ_{pⱼ,θⱼ}(ptᵢ)`.
The comparison is done entirely over `Bool`: the raw matrix bit `(matB.getD i 0).testBit j` against
the `Bool` mirror `lambdaComputeBool`, so the kernel never constructs a `ZMod 2` element.  Indexed
by `Nat < rho` via the kernel-reducible `allBelow` fold (dropping into `Fin rho` in the valid
branch), so the kernel peels one index at a time rather than materialising `List.finRange`. -/
noncomputable def checkB (a₂ a₄ a₆ : ℤ) (matB : List ℕ) (rho : ℕ)
    (lab : List (ℕ × ℤ)) (pt : List (ℚ × ℚ)) : Bool :=
  F2Invert.allBelow rho fun i =>
    F2Invert.allBelow rho fun j =>
      (matB.getD i 0).testBit j ==
        lambdaComputeBool a₂ a₄ a₆ (lab.getD j (0, 0)).1
          ((lab.getD j (0, 0)).2 : ZMod (lab.getD j (0, 0)).1) (pt.getD i (0, 0)).1

/-- If the aggregate check passes, every matrix entry equals the computed descent character.  The
`Bool` equality of `checkB` is read back into `ZMod 2` through `lambdaCompute_eq_bool`.  The point
and label families are read from the lists by `List.getD`, so the kernel never applies a
`Fin rho → _` function. -/
theorem checkB_true {a₂ a₄ a₆ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {pt : List (ℚ × ℚ)}
    (h : checkB a₂ a₄ a₆ matB rho lab pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ a₆ (lab.getD j.val (0, 0)).1
        ((lab.getD j.val (0, 0)).2 : ZMod (lab.getD j.val (0, 0)).1) (pt.getD i.val (0, 0)).1 := by
  intro i j
  simp only [checkB, F2Invert.allBelow_eq_true] at h
  have := h i.val i.isLt j.val j.isLt
  rw [lambdaCompute_eq_bool]
  simp only [F2Invert.toMat]
  rw [beq_iff_eq.mp this]

end ECCompute
