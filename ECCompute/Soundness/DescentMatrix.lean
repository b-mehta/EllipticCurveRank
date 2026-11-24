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
entry of the certificate matrix `B` equals the kernel-computed descent character
`lambdaBitK`, read into `ZMod 2`, at the matching point.
-/

namespace ECCompute

variable {a₂ a₄ : ℤ} {xnp xnm xden b : ℕ} {ls : List (ℕ × ℕ × ℕ)} {B : List ℕ}
  {pt : List (ℚ × ℚ)}

@[simp, grind =]
theorem checkBRowWord_nil : checkBRowWord a₂ a₄ xnp xnm xden [] = 0 := rfl

@[simp, grind =]
theorem checkBRowWord_cons {l : ℕ × ℕ × ℕ} :
    checkBRowWord a₂ a₄ xnp xnm xden (l :: ls) =
      lambdaBitK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden |||
        checkBRowWord a₂ a₄ xnp xnm xden ls <<< 1 := rfl

@[simp, grind =]
theorem checkBGo_cons_cons {bs : List ℕ} {p : ℚ × ℚ} {ps : List (ℚ × ℚ)} :
    checkBGo a₂ a₄ ls (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b ls).and'
        (checkBGo a₂ a₄ ls bs ps) := rfl

variable {i j : ℕ}

/-- Bit `j` of the expected row word is set iff label `j`'s descent character bit is `1`. -/
theorem testBit_checkBRowWord (hj : j < ls.length) :
    (checkBRowWord a₂ a₄ xnp xnm xden ls).testBit j ↔
      lambdaBitK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden = 1 := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem_cons_zero]
      grind [lambdaBitK_eq_zero_or_one]
    | succ k =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem_cons_succ,
        Nat.add_sub_cancel]
      obtain hb | hb := lambdaBitK_eq_zero_or_one (a₂ := a₂) (a₄ := a₄) (p := l.1) (qm := l.2.2)
        (tval := l.2.1) (xp := xnp) (xm := xnm) (xden := xden) <;>
        simp [hb, Nat.testBit_succ, ih (by simpa using hj)]

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask is set iff the descent
character bit of label `j` is `1`. -/
theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b ls) (hj : j < ls.length) :
    b.testBit j ↔ lambdaBitK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden = 1 := by
  grind [checkBRow, testBit_checkBRowWord]

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row (h : checkBGo a₂ a₄ ls B pt) (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den B[i] ls := by
  induction B generalizing pt i with grind [cases List]

/-- If the aggregate check passes, every matrix entry equals the kernel-computed descent character,
read into `ZMod 2`. -/
public theorem checkB_true {ρ : ℕ} {ls : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : ls.length = ρ)
    (hqlen : q.length = ρ)
    (h : checkB a₂ a₄ ls q B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j =
      (lambdaBitK a₂ a₄ ls[j].1 (qrMask ls[j].1) (ls[j].2 % ls[j].1).toNat
        pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den : ZMod 2) := by
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  set ns := toLs ls q with hnsdef
  have hns : ns.length = ρ := by rw [hnsdef, toLs, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : ns[j] = (ls[j].1, (ls[j].2 % ls[j].1).toNat, q[j]) := by simp [hnsdef, toLs]
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask ls[j].1`
  have hqok : qrMask ls[j].1 = q[j] := by
    have : qrMask ns[j].1 = ns[j].2.2 := by grind [checkMaskList, List.getElem_mem]
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row (i := i) hgo (by lia) (by lia)
  have hcell : (B[i] : ℕ).testBit j ↔ _ := checkBRow_true hrow (by lia)
  simp only [← Fin.getElem_fin] at hcell
  simp only [hgetN] at hcell
  rw [F2Invert.toMat_apply (by lia), hqok]
  obtain hb | hb := lambdaBitK_eq_zero_or_one (a₂ := a₂) (a₄ := a₄) (p := ls[j].1) (qm := q[j])
    (tval := (ls[j].2 % ls[j].1).toNat) (xp := pt[i].1.num.toNat) (xm := (-pt[i].1.num).toNat)
    (xden := pt[i].1.den) <;> simp [-Fin.getElem_fin, hcell, hb]

end ECCompute
