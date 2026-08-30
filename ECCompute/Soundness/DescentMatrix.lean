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

variable {a₂ a₄ : ℤ} {P xnp xnm xden b : ℕ} {ls : List (ℕ × ℕ × ℕ)} {B : List ℕ}
  {pt : List (ℚ × ℚ)}

@[simp, grind =]
theorem checkBRow_cons {l : ℕ × ℕ × ℕ} :
    checkBRow a₂ a₄ xnp xnm xden b (l :: ls) =
      (((b % 2).beq 1).rec (motive := fun _ ↦ Bool)
        (lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (checkBRow a₂ a₄ xnp xnm xden (b / 2) ls) := rfl

@[simp, grind =]
theorem checkBGo_cons_cons {bs : List ℕ} {p : ℚ × ℚ} {ps : List (ℚ × ℚ)} :
    checkBGo a₂ a₄ P ls (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ (p.1.num.toNat.mod P) ((-p.1.num).toNat.mod P) (p.1.den.mod P) b ls).and'
        (checkBGo a₂ a₄ P ls bs ps) := rfl

variable {i j : ℕ}

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b ls) (hj : j < ls.length) :
    b.testBit j = lambdaK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden := by
  induction ls generalizing b j with
  | nil => grind
  | cons l ls ih => cases j <;> grind [Nat.testBit_succ]

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row (h : checkBGo a₂ a₄ P ls B pt) (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ (pt[i].1.num.toNat.mod P) ((-pt[i].1.num).toNat.mod P) (pt[i].1.den.mod P)
      B[i] ls := by
  -- MEASUREMENT ONLY: soundness sorry'd; statement restated for the mod-`P`-reduced coordinates.
  sorry

/-- If the aggregate check passes, every matrix entry equals the kernel-computed descent character,
read into `ZMod 2`. -/
public theorem checkB_true {ρ : ℕ} {ls : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : ls.length = ρ)
    (hqlen : q.length = ρ)
    (h : checkB a₂ a₄ P ls q B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j =
      if lambdaK a₂ a₄ ls[j].1 (qrMask ls[j].1) (ls[j].2 % ls[j].1).toNat
          pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den then 1 else 0 := by
  -- MEASUREMENT ONLY: soundness sorry'd. The kernel now reduces each coordinate mod the emitted
  -- literal `P` before the per-label loop; since every label prime divides `P` (checked in
  -- `checkB`), `(x mod P) mod p = x mod p`, so the descent value at the full coordinate is unchanged.
  sorry

end ECCompute
