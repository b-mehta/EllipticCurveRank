/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Soundness.F2Invert
public import ECCompute.Soundness.LambdaCompute

import Mathlib.Data.Nat.Bitwise
import ECCompute.ForLean

/-!
# Soundness of the descent-matrix check

`checkB_true` proves the kernel-reducible `checkB` (`ECCompute.Kernel`) sound: when it passes, every
entry of the certificate matrix `B` equals the abstract descent character `lambdaCompute` at the
matching point.
-/

namespace ECCompute

variable {a₂ a₄ : ℤ} {xnp xnm xden b : ℕ} {ls : List (ℕ × ℕ × ℕ)} {B : List ℕ}
  {pt : List (ℚ × ℚ)}

@[simp, grind =]
theorem checkBRow_cons {l : ℕ × ℕ × ℕ} {ls : List (ℕ × ℕ × ℕ)} :
    checkBRow a₂ a₄ xnp xnm xden b (l :: ls) =
      (((b % 2).beq 1).rec (motive := fun _ ↦ Bool)
        (lambdaComputeBoolNatMask a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaComputeBoolNatMask a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (checkBRow a₂ a₄ xnp xnm xden (b / 2) ls) := rfl

@[simp, grind =]
theorem checkBGo_cons_cons {bs : List ℕ} {p : ℚ × ℚ} {ps : List (ℚ × ℚ)} :
    checkBGo a₂ a₄ ls (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b ls).and'
        (checkBGo a₂ a₄ ls bs ps) := rfl

variable {i j : ℕ}

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b ls) {j : ℕ} (hj : j < ls.length) :
    b.testBit j = lambdaComputeBoolNatMask a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden := by
  induction ls generalizing b j with
  | nil => grind
  | cons l ls ih =>
    cases j <;> grind [Nat.testBit_succ]

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row (h : checkBGo a₂ a₄ ls B pt) (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ pt[i].1.num.toNat (-pt[i].1.num).toNat
      pt[i].1.den B[i] ls := by
  induction B generalizing pt i with grind [cases List]

/-- If `checkMaskList` passes, every supplied mask equals `qrMask` of its label's prime. -/
theorem checkMaskList_true (h : checkMaskList ls) {j : ℕ} (hj : j < ls.length) :
    qrMask ls[j].1 = ls[j].2.2 := by
  grind [checkMaskList, List.getElem_mem]

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
public theorem checkB_true {ρ : ℕ} {lab : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : lab.length = ρ)
    (hqlen : q.length = ρ)
    (hpr : ∀ j : Fin ρ, lab[j].1.Prime)
    (h : checkB a₂ a₄ lab q B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j = lambdaCompute a₂ a₄ lab[j].1 lab[j].2 pt[i].1 := by
  set L := lab[j] with hL
  set P := pt[i] with hP
  -- The row and column lemmas below index by `ℕ`, so read the label and point through `Fin.val`.
  simp only [Fin.getElem_fin] at hL hP
  have hp : 0 < L.1 := (hpr j).pos
  set ls := toLabN lab q with hlsdef
  have hls : ls.length = ρ := by
    rw [hlsdef, toLabN, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : ls[j.val]'(by rw [hls]; exact j.isLt)
      = (L.1, (L.2 % (L.1 : ℤ)).toNat, q[j]) := by
    simp only [hlsdef, toLabN, List.getElem_zipWith, Fin.getElem_fin, ← Int.mod_def', ← hL]
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask L.1`
  have hqok : qrMask L.1 = q[j] := by
    have := checkMaskList_true hmask (by rw [hls]; exact j.isLt)
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row (i := i) hgo (by lia) (by lia)
  have hcell := checkBRow_true (j := j) hrow (by lia)
  rw [hgetN] at hcell
  -- rewrite the supplied mask to `qrMask L.1`, then bridge the mask cell to `lambdaComputeBool`
  rw [← hqok, ← hP] at hcell
  have hbridge : lambdaComputeBoolNatMask a₂ a₄
      L.1 (qrMask L.1) (L.2 % L.1).toNat P.1.num.toNat (-P.1.num).toNat P.1.den
        = lambdaComputeBool a₂ a₄ L.1 L.2 P.1 :=
    lambdaComputeBoolNatMask_eq hp
      (intResNat_cast hp.ne') (Int.toNat_sub_toNat_neg P.1.num).symm rfl
  rw [F2Invert.toMat_apply (by lia), Fin.getElem_fin, hcell, hbridge, lambdaCompute_eq_bool]

end ECCompute
