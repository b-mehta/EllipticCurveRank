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
`lambdaK`, read into `ZMod 2`, at the matching point.
-/

namespace ECCompute

variable {a₂ a₄ : ℤ} {xnp xnm xden b : ℕ} {ls : List (ℕ × ℕ × ℕ)} {B : List ℕ}
  {pt : List (ℕ × Bool × ℕ × ℕ × ℕ)}

@[simp, grind =]
theorem checkBRowWord_cons {l : ℕ × ℕ × ℕ} :
    checkBRowWord a₂ a₄ xnp xnm xden (l :: ls) =
      lambdaBitK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden |||
        checkBRowWord a₂ a₄ xnp xnm xden ls <<< 1 := rfl

@[simp, grind =]
theorem checkBGo_cons_cons {bs : List ℕ} {p : ℕ × Bool × ℕ × ℕ × ℕ}
    {ps : List (ℕ × Bool × ℕ × ℕ × ℕ)} :
    checkBGo a₂ a₄ ls (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ (Bool.rec (motive := fun _ ↦ ℕ) p.1 0 p.2.1)
          (Bool.rec (motive := fun _ ↦ ℕ) 0 p.1 p.2.1) p.2.2.1 b ls).and'
        (checkBGo a₂ a₄ ls bs ps) := rfl

variable {i j : ℕ}

/-- `lambdaBitK` is the `Nat` bit `0`/`1` of the `Bool` descent character `lambdaK`. -/
theorem lambdaBitK_eq {p qmask tval xp xm xden : ℕ} :
    lambdaBitK a₂ a₄ p qmask tval xp xm xden =
      if lambdaK a₂ a₄ p qmask tval xp xm xden then 1 else 0 := by
  have key (X : ℕ) : qmask >>> X % 2 ^^^ 1 = if qrLookupBool qmask X = false then 1 else 0 := by
    rw [qrLookupBool]
    rcases Nat.mod_two_eq_zero_or_one (qmask >>> X) with h | h <;>
      simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, h] <;> decide
  rw [lambdaBitK, lambdaK]
  cases (xden.mod p).beq 0 <;> cases (alphaResK p tval xp xm xden).beq 0 <;> simp [key]

/-- Bit `j` of the expected row word equals label `j`'s `Bool` descent character. -/
theorem testBit_checkBRowWord (hj : j < ls.length) :
    (checkBRowWord a₂ a₄ xnp xnm xden ls).testBit j =
      lambdaK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, lambdaBitK_eq,
        List.getElem_cons_zero]
      cases lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden <;> simp
    | succ k =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, lambdaBitK_eq,
        List.getElem_cons_succ, Nat.add_sub_cancel, ih (by simpa using hj)]
      cases lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden <;> simp [Nat.testBit_succ]

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b ls) (hj : j < ls.length) :
    b.testBit j = lambdaK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden := by
  rw [checkBRow] at hb
  rw [← Nat.eq_of_beq_eq_true hb]
  exact testBit_checkBRowWord hj

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row (h : checkBGo a₂ a₄ ls B pt) (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ (Bool.rec (motive := fun _ ↦ ℕ) pt[i].1 0 pt[i].2.1)
      (Bool.rec (motive := fun _ ↦ ℕ) 0 pt[i].1 pt[i].2.1) pt[i].2.2.1 B[i] ls := by
  induction B generalizing pt i with grind [cases List]

/-- If the aggregate check passes, every matrix entry equals the kernel-computed descent character,
read into `ZMod 2`. -/
public theorem checkB_true {ρ : ℕ} {ls : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : ls.length = ρ)
    (hqlen : q.length = ρ)
    (h : checkB a₂ a₄ ls q B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j =
      if lambdaK a₂ a₄ ls[j].1 (qrMask ls[j].1) (ls[j].2 % ls[j].1).toNat
          (Bool.rec (motive := fun _ ↦ ℕ) pt[i].1 0 pt[i].2.1)
          (Bool.rec (motive := fun _ ↦ ℕ) 0 pt[i].1 pt[i].2.1) pt[i].2.2.1 then 1 else 0 := by
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  set L := ls[j]
  set ns := toLs ls q with hnsdef
  have hns : ns.length = ρ := by rw [hnsdef, toLs, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : ns[j] = (L.1, (L.2 % L.1).toNat, q[j]) := by simp [hnsdef, toLs, L]
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask L.1`
  have hqok : qrMask L.1 = q[j] := by
    have : qrMask ns[j].1 = ns[j].2.2 := by grind [checkMaskList, List.getElem_mem]
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row (i := i) hgo (by lia) (by lia)
  have hcell : B[i].testBit j = _ := checkBRow_true hrow (by lia)
  simp only [← Fin.getElem_fin] at hcell
  rw [hgetN] at hcell
  rw [F2Invert.toMat_apply (by lia), hqok, hcell]

end ECCompute
