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

/-- `l.getD n d` is a genuine member of `l` when the index is in range. -/
theorem getD_mem_of_lt {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- `getD` commutes with `zipWith` on equal-length lists in range. -/
private theorem getD_zipWith {α β γ : Type*} (f : α → β → γ) (as : List α) (bs : List β) (n : ℕ)
    (da : α) (db : β) (dc : γ) (hn : n < as.length) (hlen : as.length = bs.length) :
    (List.zipWith f as bs).getD n dc = f (as.getD n da) (bs.getD n db) := by
  induction as generalizing bs n with
  | nil => simp at hn
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih bs n (by simpa using hn) (by simpa using hlen)

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
      ∀ j, j < labN.length → b.testBit j = lambdaComputeBoolNatMask c2p c2m c4p c4m
        (labN.getD j (0, 0, 0)).1 (labN.getD j (0, 0, 0)).2.2 (labN.getD j (0, 0, 0)).2.1
        xnp xnm xden := by
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
      ∀ i, i < matB.length → i < pt.length →
        checkBRow c2p c2m c4p c4m (pt.getD i (0, 0)).1.num.toNat (-(pt.getD i (0, 0)).1.num).toNat
          (pt.getD i (0, 0)).1.den (matB.getD i 0) labN = true := by
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
    ∀ j, j < labN.length → qrMask (labN.getD j (0, 0, 0)).1 = (labN.getD j (0, 0, 0)).2.2 := by
  rw [checkMaskList, allList_eq_true] at h
  intro j hj
  exact Nat.eq_of_beq_eq_true (h _ (getD_mem_of_lt hj))

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {a₂ a₄ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {qms : List ℕ} {pt : List (ℚ × ℚ)}
    (hBlen : matB.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (hqlen : qms.length = rho)
    (hpr : ∀ j : Fin rho, ((lab.getD j.val (0, 0)).1).Prime)
    (hp2 : ∀ j : Fin rho, (lab.getD j.val (0, 0)).1 ≠ 2)
    (h : checkB a₂ a₄ lab qms matB pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ (lab.getD j.val (0, 0)).1
        ((lab.getD j.val (0, 0)).2 : ZMod (lab.getD j.val (0, 0)).1) (pt.getD i.val (0, 0)).1 := by
  intro i j
  set L : ℕ × ℤ := lab.getD j.val (0, 0) with hL
  set P : ℚ × ℚ := pt.getD i.val (0, 0) with hP
  have hp : 0 < L.1 := (hpr j).pos
  haveI : Fact L.1.Prime := ⟨hpr j⟩
  set labN := toLabN lab qms with hlabNdef
  have hlabN : labN.length = rho := by
    rw [hlabNdef, toLabN, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : labN.getD j.val (0, 0, 0) = (L.1, (L.2 % (L.1 : ℤ)).toNat, qms.getD j.val 0) := by
    rw [hlabNdef, toLabN, getD_zipWith _ _ _ _ (0, 0) 0 _ (by rw [hllen]; exact j.isLt)
      (by rw [hllen, hqlen]), ← Int.mod_def', ← hL]
  rw [checkB, Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hmask, hgo⟩ := h
  -- the supplied mask for column `j` is `qrMask L.1`
  have hqok : qrMask L.1 = qms.getD j.val 0 := by
    have := checkMaskList_true hmask j.val (by rw [hlabN]; exact j.isLt)
    rwa [hgetN] at this
  -- read off the mask-based cell value at `(i, j)`
  have hrow := checkBGo_row hgo i.val (hBlen ▸ i.isLt) (hplen ▸ i.isLt)
  have hcell := checkBRow_true hrow j.val (by rw [hlabN]; exact j.isLt)
  rw [hgetN] at hcell
  -- rewrite the supplied mask to `qrMask L.1`, then bridge the mask cell to `lambdaComputeBool`
  rw [← hqok] at hcell
  have hbridge : lambdaComputeBoolNatMask a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat
      L.1 (qrMask L.1) (L.2 % (L.1 : ℤ)).toNat P.1.num.toNat (-P.1.num).toNat P.1.den
      = lambdaComputeBool a₂ a₄ L.1 (L.2 : ZMod L.1) P.1 :=
    lambdaComputeBoolNatMask_eq a₂ a₄ L.1 hp (L.2 : ZMod L.1) P.1 _ _ _ _ _ _ _ _
      (int_toNat_sub a₂) (int_toNat_sub a₄) (intResNat_cast hp L.2)
      (int_toNat_sub P.1.num) rfl
  rw [F2Invert.toMat, hcell, hbridge, lambdaCompute_eq_bool]

end ECCompute
