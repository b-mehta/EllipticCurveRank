/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness.F2Invert
import ECCompute.Soundness.LambdaCompute
import ECCompute.Soundness.IntResNat
import ECCompute.Soundness.Fold

/-!
# Aggregate descent-character matrix check

`checkB` is a single `Bool` that tests every entry of the certificate matrix `matB` against the
computed descent character; `checkB_true` recovers the individual entry equalities from
`checkB … = true`.

The kernel-reduced work runs through `lambdaComputeBoolNatMask`, evaluating every entry in `Nat`
and reading each label's Legendre character from a precomputed quadratic-residue mask. The
signed inputs are turned into `Nat` pieces once: the coefficients `a₂`, `a₄` and each point's
numerator become `mp - mn` pairs via `Int.toNat`, each label representative `θ : ℤ` becomes its
residue `(θ % p).toNat`, and each label carries its quadratic-residue mask `q`. `checkMaskList`
verifies each supplied mask equals `qrMask p` once per prime.
-/

namespace ECCompute

open Matrix Finset

/-- Turn the `(prime, θ)` labels and their quadratic-residue masks into the `Nat` label triples
`(p, (θ % p).toNat, q)` consumed by the kernel-reduced checker. -/
noncomputable def toLabN (lab : List (ℕ × ℤ)) (qms : List ℕ) : List (ℕ × ℕ × ℕ) :=
  List.zipWith (fun l q => (l.1, (Int.emod l.2 (l.1 : ℤ)).toNat, q)) lab qms

/-- One row of the descent-matrix check: for the row bitmask `b`, the point's `Nat` pieces and the
coefficient pairs, fold over the `Nat` label triples `labN = (p, tval, q)`, consuming `b` one bit at
a time, comparing each against the mask-based `Nat`-valued descent character. -/
noncomputable def checkBRow (c2p c2m c4p c4m xnp xnm xden b : ℕ) (labN : List (ℕ × ℕ × ℕ)) : Bool :=
  labN.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih b =>
      ((Nat.beq (Nat.mod b 2) 1).rec (motive := fun _ => Bool)
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (ih (Nat.div b 2))) b

theorem checkBRow_cons (c2p c2m c4p c4m xnp xnm xden b : ℕ) (l : ℕ × ℕ × ℕ)
    (ls : List (ℕ × ℕ × ℕ)) :
    checkBRow c2p c2m c4p c4m xnp xnm xden b (l :: ls) =
      ((Nat.beq (b % 2) 1).rec (motive := fun _ => Bool)
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden).not'
        (lambdaComputeBoolNatMask c2p c2m c4p c4m l.1 l.2.2 l.2.1 xnp xnm xden)).and'
        (checkBRow c2p c2m c4p c4m xnp xnm xden (b / 2) ls) := rfl

/-- Fold over the rows, pairing each row bitmask of `matB` with its point in `pt`, and check each
row with `checkBRow`. The point's numerator is split into `x.num.toNat - (-x.num).toNat`. -/
noncomputable def checkBGo (c2p c2m c4p c4m : ℕ) (labN : List (ℕ × ℕ × ℕ)) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  matB.rec (motive := fun _ => List (ℚ × ℚ) → Bool) (fun _ => true)
    (fun b _ ih pt => pt.rec (motive := fun _ => Bool) true
      (fun p ps _ => (checkBRow c2p c2m c4p c4m p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (ih ps))) pt

theorem checkBGo_cons_cons (c2p c2m c4p c4m : ℕ) (labN : List (ℕ × ℕ × ℕ)) (b : ℕ) (bs : List ℕ)
    (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    checkBGo c2p c2m c4p c4m labN (b :: bs) (p :: ps) =
      (checkBRow c2p c2m c4p c4m p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (checkBGo c2p c2m c4p c4m labN bs ps) := rfl

/-- Verify every supplied mask: for each label triple `(p, _, q)`, `q` must equal `qrMask p`. -/
noncomputable def checkMaskList (labN : List (ℕ × ℕ × ℕ)) : Bool :=
  allList (fun l => (qrMask l.1).beq l.2.2) labN

/-- The aggregate descent-matrix check. The coefficients become `mp - mn` pairs and the labels their
`Nat` residues and masks once, up front; the masks are verified by `checkMaskList` and then
`checkBGo` folds the rows entirely in `Nat`. -/
noncomputable def checkB (a₂ a₄ : ℤ) (lab : List (ℕ × ℤ)) (qms : List ℕ) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  (checkMaskList (toLabN lab qms)).and'
    (checkBGo a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat (toLabN lab qms) matB pt)

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true {c2p c2m c4p c4m xnp xnm xden : ℕ} :
    ∀ {b : ℕ} {labN : List (ℕ × ℕ × ℕ)}, checkBRow c2p c2m c4p c4m xnp xnm xden b labN = true →
      ∀ j, (hj : j < labN.length) → b.testBit j = lambdaComputeBoolNatMask c2p c2m c4p c4m
        labN[j].1 labN[j].2.2 labN[j].2.1 xnp xnm xden := by
  intro b labN
  induction labN generalizing b with
  | nil => grind
  | cons l ls ih =>
    intro hb j hj
    simp only [checkBRow_cons, Bool.and'_eq_and, Bool.and_eq_true] at hb
    obtain ⟨h0, hrec⟩ := hb
    have hbe := (by decide : ∀ x y : Bool, (x.rec y.not' y = true) → x = y) _ _ h0
    cases j <;> grind [Nat.testBit_succ, Nat.beq_eq]

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row {c2p c2m c4p c4m : ℕ} {labN : List (ℕ × ℕ × ℕ)} :
    ∀ {matB : List ℕ} {pt : List (ℚ × ℚ)}, checkBGo c2p c2m c4p c4m labN matB pt = true →
      ∀ i, (hi : i < matB.length) → (hip : i < pt.length) →
        checkBRow c2p c2m c4p c4m pt[i].1.num.toNat (-pt[i].1.num).toNat
          pt[i].1.den matB[i] labN = true := by
  intro matB
  induction matB with
  | nil => grind
  | cons b bs ih =>
    intro pt h i hi hip
    cases pt with
    | nil => grind
    | cons p ps =>
      simp only [checkBGo_cons_cons, Bool.and'_eq_and, Bool.and_eq_true] at h
      cases i <;> grind

/-- If `checkMaskList` passes, every supplied mask equals `qrMask` of its label's prime. -/
theorem checkMaskList_true {labN : List (ℕ × ℕ × ℕ)} (h : checkMaskList labN = true) :
    ∀ j, (hj : j < labN.length) → qrMask labN[j].1 = labN[j].2.2 := by
  rw [checkMaskList, allList_eq_true] at h
  intro j hj
  exact Nat.eq_of_beq_eq_true (h _ (List.getElem_mem hj))

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {a₂ a₄ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {qms : List ℕ} {pt : List (ℚ × ℚ)}
    (hBlen : matB.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (hqlen : qms.length = rho)
    (hpr : ∀ j : Fin rho, (lab[j].1).Prime)
    (hp2 : ∀ j : Fin rho, lab[j].1 ≠ 2)
    (h : checkB a₂ a₄ lab qms matB pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ lab[j].1 ((lab[j].2 : ZMod lab[j].1)) pt[i].1 := by
  intro i j
  set L : ℕ × ℤ := lab[j] with hL
  set P : ℚ × ℚ := pt[i] with hP
  -- The row and column lemmas below index by `ℕ`, so read the label and point through `Fin.val`.
  simp only [Fin.getElem_fin] at hL hP
  have hp : 0 < L.1 := (hpr j).pos
  have : Fact L.1.Prime := ⟨hpr j⟩
  have : NeZero L.1 := ⟨hp.ne'⟩
  set labN := toLabN lab qms with hlabNdef
  have hlabN : labN.length = rho := by
    rw [hlabNdef, toLabN, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : labN[j.val]'(by rw [hlabN]; exact j.isLt)
      = (L.1, (L.2 % (L.1 : ℤ)).toNat, qms[j]) := by
    simp only [hlabNdef, toLabN, List.getElem_zipWith, Fin.getElem_fin, ← Int.mod_def', ← hL]
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask L.1`
  have hqok : qrMask L.1 = qms[j] := by
    have := checkMaskList_true hmask j.val (by rw [hlabN]; exact j.isLt)
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row hgo i.val (hBlen ▸ i.isLt) (hplen ▸ i.isLt)
  have hcell := checkBRow_true hrow j.val (by rw [hlabN]; exact j.isLt)
  rw [hgetN] at hcell
  -- rewrite the supplied mask to `qrMask L.1`, then bridge the mask cell to `lambdaComputeBool`
  rw [← hqok, ← hP] at hcell
  have hbridge : lambdaComputeBoolNatMask a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat
      L.1 (qrMask L.1) (L.2 % (L.1 : ℤ)).toNat P.1.num.toNat (-P.1.num).toNat P.1.den
      = lambdaComputeBool a₂ a₄ L.1 (L.2 : ZMod L.1) P.1 :=
    lambdaComputeBoolNatMask_eq a₂ a₄ L.1 hp (L.2 : ZMod L.1) P.1 _ _ _ _ _ _ _ _
      (int_toNat_sub a₂) (int_toNat_sub a₄) (intResNat_cast hp.ne' L.2)
      (int_toNat_sub P.1.num) rfl
  rw [F2Invert.toMat_apply (by rw [hBlen]; exact i.isLt), Fin.getElem_fin, hcell, hbridge,
    lambdaCompute_eq_bool]

end ECCompute
