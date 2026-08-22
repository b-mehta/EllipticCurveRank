/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Kernel
import ECCompute.Soundness.F2Invert
import ECCompute.Soundness.LambdaCompute
import ECCompute.Soundness.IntResNat
import ECCompute.Soundness.Fold

/-!
# Soundness of the descent-matrix check

`checkB_true` proves the kernel-reducible `checkB` (`ECCompute.Kernel`) sound: when it passes, every
entry of the certificate matrix `B` equals the abstract descent character `lambdaCompute` at the
matching point.
-/

namespace ECCompute

variable {a₂ a₄ : ℤ} {xnp xnm xden b : ℕ} {labN : List (ℕ × ℕ × ℕ)} {B : List ℕ}
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
    checkBGo a₂ a₄ labN (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (checkBGo a₂ a₄ labN bs ps) := rfl

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b labN) (j : ℕ)
    (hj : j < labN.length) :
    b.testBit j = lambdaComputeBoolNatMask a₂ a₄
      labN[j].1 labN[j].2.2 labN[j].2.1 xnp xnm xden := by
  induction labN generalizing b j with
  | nil => grind
  | cons l ls ih =>
    simp only [checkBRow_cons, Bool.and'_eq_and, Bool.and_eq_true] at hb
    obtain ⟨h0, hrec⟩ := hb
    have hbe := (by decide : ∀ x y : Bool, (x.rec y.not' y = true) → x = y) _ _ h0
    cases j <;> grind [Nat.testBit_succ, Nat.beq_eq]

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row (h : checkBGo a₂ a₄ labN B pt) (i : ℕ)
    (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ pt[i].1.num.toNat (-pt[i].1.num).toNat
      pt[i].1.den B[i] labN := by
  induction B generalizing pt i with
  | nil => grind
  | cons b bs ih =>
    cases pt with
    | nil => grind
    | cons p ps => cases i <;> grind

/-- If `checkMaskList` passes, every supplied mask equals `qrMask` of its label's prime. -/
theorem checkMaskList_true (h : checkMaskList labN) (j : ℕ) (hj : j < labN.length) :
    qrMask labN[j].1 = labN[j].2.2 := by
  grind [checkMaskList, List.getElem_mem]

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {rho : ℕ} {lab : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (hqlen : q.length = rho)
    (hpr : ∀ j : Fin rho, (lab[j].1).Prime)
    (h : checkB a₂ a₄ lab q B pt) (i j : Fin rho) :
    F2Invert.toMat B rho i j =
      lambdaCompute a₂ a₄ lab[j].1 ((lab[j].2 : ZMod lab[j].1)) pt[i].1 := by
  set L := lab[j] with hL
  set P := pt[i] with hP
  -- The row and column lemmas below index by `ℕ`, so read the label and point through `Fin.val`.
  simp only [Fin.getElem_fin] at hL hP
  have hp : 0 < L.1 := (hpr j).pos
  have : Fact L.1.Prime := ⟨hpr j⟩
  have : NeZero L.1 := ⟨hp.ne'⟩
  set labN := toLabN lab q with hlabNdef
  have hlabN : labN.length = rho := by
    rw [hlabNdef, toLabN, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : labN[j.val]'(by rw [hlabN]; exact j.isLt)
      = (L.1, (L.2 % (L.1 : ℤ)).toNat, q[j]) := by
    simp only [hlabNdef, toLabN, List.getElem_zipWith, Fin.getElem_fin, ← Int.mod_def', ← hL]
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask L.1`
  have hqok : qrMask L.1 = q[j] := by
    have := checkMaskList_true hmask j.val (by rw [hlabN]; exact j.isLt)
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row hgo i.val (hBlen ▸ i.isLt) (hplen ▸ i.isLt)
  have hcell := checkBRow_true hrow j.val (by rw [hlabN]; exact j.isLt)
  rw [hgetN] at hcell
  -- rewrite the supplied mask to `qrMask L.1`, then bridge the mask cell to `lambdaComputeBool`
  rw [← hqok, ← hP] at hcell
  have hbridge : lambdaComputeBoolNatMask a₂ a₄
      L.1 (qrMask L.1) (L.2 % (L.1 : ℤ)).toNat P.1.num.toNat (-P.1.num).toNat P.1.den
      = lambdaComputeBool a₂ a₄ L.1 (L.2 : ZMod L.1) P.1 :=
    lambdaComputeBoolNatMask_eq a₂ a₄ L.1 hp (L.2 : ZMod L.1) P.1 _ _ _ _
      (intResNat_cast hp.ne' L.2) (int_toNat_sub P.1.num) rfl
  rw [F2Invert.toMat_apply (by rw [hBlen]; exact i.isLt), Fin.getElem_fin, hcell, hbridge,
    lambdaCompute_eq_bool]

end ECCompute
