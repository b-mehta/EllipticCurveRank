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
Indexed by `Nat < rho` via the kernel-reducible `allBelow` fold (dropping into `Fin rho` in the
valid branch), so the kernel peels one index at a time rather than materialising `List.finRange`. -/
noncomputable def checkB (a₂ a₄ a₆ : ℤ) (matB : List ℕ) (rho : ℕ)
    (lab : Fin rho → ℕ × ℤ) (pt : Fin rho → ℚ × ℚ) : Bool :=
  F2Invert.allBelow rho fun i =>
    F2Invert.allBelow rho fun j =>
      if hi : i < rho then if hj : j < rho then
        F2Invert.toMat matB rho ⟨i, hi⟩ ⟨j, hj⟩ ==
          lambdaCompute a₂ a₄ a₆ (lab ⟨j, hj⟩).1 ((lab ⟨j, hj⟩).2 : ZMod (lab ⟨j, hj⟩).1)
            (pt ⟨i, hi⟩).1
      else true else true

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {a₂ a₄ a₆ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : Fin rho → ℕ × ℤ} {pt : Fin rho → ℚ × ℚ}
    (h : checkB a₂ a₄ a₆ matB rho lab pt = true) :
    ∀ i j, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1 := by
  intro i j
  simp only [checkB, F2Invert.allBelow_eq_true] at h
  have := h i.val i.isLt j.val j.isLt
  rw [dif_pos i.isLt, dif_pos j.isLt, Fin.eta, Fin.eta] at this
  exact beq_iff_eq.mp this

end ECCompute
