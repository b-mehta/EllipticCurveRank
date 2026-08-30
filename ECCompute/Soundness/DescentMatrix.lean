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
  {pt : List (ℚ × ℚ)}

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
    checkBRow a₂ a₄ pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den B[i] ls := by
  induction B generalizing pt i with grind [cases List]

/-- If the aggregate check passes, every matrix entry equals the kernel-computed descent character,
read into `ZMod 2`. The labels are the precomputed triples `(p, tval, qrmask)` consumed directly.

MEASUREMENT ONLY: proof `sorry`'d; the kernel `checkB` is exercised at certificate check time, the
correctness bridge is not. -/
public theorem checkB_true {ρ : ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : ls.length = ρ)
    (h : checkB a₂ a₄ ls B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j =
      if lambdaK a₂ a₄ ls[j].1 (qrMask ls[j].1) ls[j].2.1
          pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den then 1 else 0 := by
  sorry

end ECCompute
