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

The kernel-reduced work runs through `lambdaComputeBoolNat`, so every entry is evaluated in `Nat`
with no `ZMod` or `Int` arithmetic. The signed inputs are turned into `Nat` pieces once: the
coefficients `a₂`, `a₄` and each point's numerator become `mp - mn` pairs via `Int.toNat`, and each
label representative `θ : ℤ` becomes its residue `(θ % p).toNat`.
-/

namespace ECCompute

/-- One row of the descent-matrix check: for the row bitmask `b`, the point's `Nat` pieces and the
coefficient pairs, fold over the `Nat` labels `labN = (p, tval)`, consuming `b` one bit at a time,
comparing each against the `Nat`-valued descent character. -/
noncomputable def checkBRow (c2p c2m c4p c4m xnp xnm xden b : ℕ) (labN : List (ℕ × ℕ)) : Bool :=
  labN.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih b =>
      (beqBool (b.testBit 0) (lambdaComputeBoolNat c2p c2m c4p c4m l.1 l.2 xnp xnm xden)).and'
        (ih (b.shiftRight 1))) b

theorem checkBRow_cons (c2p c2m c4p c4m xnp xnm xden b : ℕ) (l : ℕ × ℕ) (ls : List (ℕ × ℕ)) :
    checkBRow c2p c2m c4p c4m xnp xnm xden b (l :: ls) =
      (beqBool (b.testBit 0) (lambdaComputeBoolNat c2p c2m c4p c4m l.1 l.2 xnp xnm xden)).and'
        (checkBRow c2p c2m c4p c4m xnp xnm xden (b >>> 1) ls) := rfl

/-- Fold over the rows, pairing each row bitmask of `matB` with its point in `pt`, and check each
row with `checkBRow`. The point's numerator is split into `x.num.toNat - (-x.num).toNat`. -/
noncomputable def checkBGo (c2p c2m c4p c4m : ℕ) (labN : List (ℕ × ℕ)) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  matB.rec (motive := fun _ => List (ℚ × ℚ) → Bool) (fun _ => true)
    (fun b _ ih pt => pt.rec (motive := fun _ => Bool) true
      (fun p ps _ => (checkBRow c2p c2m c4p c4m p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (ih ps))) pt

theorem checkBGo_cons_cons (c2p c2m c4p c4m : ℕ) (labN : List (ℕ × ℕ)) (b : ℕ) (bs : List ℕ)
    (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    checkBGo c2p c2m c4p c4m labN (b :: bs) (p :: ps) =
      (checkBRow c2p c2m c4p c4m p.1.num.toNat (-p.1.num).toNat p.1.den b labN).and'
        (checkBGo c2p c2m c4p c4m labN bs ps) := rfl

/-- The aggregate descent-matrix check. The coefficients become `mp - mn` pairs and the labels their
`Nat` residues once, up front; then `checkBGo` folds the rows entirely in `Nat`. -/
noncomputable def checkB (a₂ a₄ _a₆ : ℤ) (lab : List (ℕ × ℤ)) (matB : List ℕ)
    (pt : List (ℚ × ℚ)) : Bool :=
  checkBGo a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat
    (lab.map fun l => (l.1, (l.2 % (l.1 : ℤ)).toNat)) matB pt

/-- Row correctness: if `checkBRow` passes, bit `j` of the row bitmask equals the `Bool` descent
character of label `j`. -/
theorem checkBRow_true {c2p c2m c4p c4m xnp xnm xden : ℕ} :
    ∀ {b : ℕ} {labN : List (ℕ × ℕ)}, checkBRow c2p c2m c4p c4m xnp xnm xden b labN = true →
      ∀ j, j < labN.length → b.testBit j = lambdaComputeBoolNat c2p c2m c4p c4m
        (labN.getD j (0, 0)).1 (labN.getD j (0, 0)).2 xnp xnm xden := by
  intro b labN
  induction labN generalizing b with
  | nil => grind
  | cons l ls ih =>
    intro hb j hj
    simp only [checkBRow_cons, beqBool_eq, Bool.and'_eq_and, Bool.and_eq_true, beq_iff_eq] at hb
    cases j <;> grind

/-- Row extraction: if the aggregate check passes, row `i`'s bitmask passes `checkBRow`. -/
theorem checkBGo_row {c2p c2m c4p c4m : ℕ} {labN : List (ℕ × ℕ)} :
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

/-- If the aggregate check passes, every matrix entry equals the computed descent character. -/
theorem checkB_true {a₂ a₄ a₆ : ℤ} {matB : List ℕ} {rho : ℕ}
    {lab : List (ℕ × ℤ)} {pt : List (ℚ × ℚ)}
    (hBlen : matB.length = rho) (hplen : pt.length = rho) (hllen : lab.length = rho)
    (hp : ∀ j : Fin rho, 0 < (lab.getD j.val (0, 0)).1)
    (h : checkB a₂ a₄ a₆ lab matB pt = true) :
    ∀ i j : Fin rho, F2Invert.toMat matB rho i j =
      lambdaCompute a₂ a₄ a₆ (lab.getD j.val (0, 0)).1
        ((lab.getD j.val (0, 0)).2 : ZMod (lab.getD j.val (0, 0)).1) (pt.getD i.val (0, 0)).1 := by
  intro i j
  set L : ℕ × ℤ := lab.getD j.val (0, 0) with hL
  set P : ℚ × ℚ := pt.getD i.val (0, 0) with hP
  have hlabN : (lab.map fun l => (l.1, (l.2 % (l.1 : ℤ)).toNat)).length = rho := by
    rw [List.length_map, hllen]
  have hgetN : (lab.map fun l => (l.1, (l.2 % (l.1 : ℤ)).toNat)).getD j.val (0, 0)
      = (L.1, (L.2 % (L.1 : ℤ)).toNat) := by
    have hm := List.getD_map (l := lab) (n := j.val) (d := ((0 : ℕ), (0 : ℤ)))
      (f := fun l => (l.1, (l.2 % (l.1 : ℤ)).toNat))
    simpa [hL] using hm
  rw [checkB] at h
  have hrow := checkBGo_row h i.val (hBlen ▸ i.isLt) (hplen ▸ i.isLt)
  have hcell := checkBRow_true hrow j.val (by rw [hlabN]; exact j.isLt)
  rw [hgetN] at hcell
  -- `lambdaComputeBoolNat` on the residue pieces equals the `ZMod` `lambdaComputeBool`.
  have hbridge : lambdaComputeBoolNat a₂.toNat (-a₂).toNat a₄.toNat (-a₄).toNat
      L.1 (L.2 % (L.1 : ℤ)).toNat P.1.num.toNat (-P.1.num).toNat P.1.den
      = lambdaComputeBool a₂ a₄ a₆ L.1 (L.2 : ZMod L.1) P.1 :=
    lambdaComputeBoolNat_eq a₂ a₄ a₆ L.1 (hp j) (L.2 : ZMod L.1) P.1 _ _ _ _ _ _ _ _
      (int_toNat_sub a₂) (int_toNat_sub a₄) (intModToNat_cast (hp j) L.2)
      (int_toNat_sub P.1.num) rfl
  rw [F2Invert.toMat, hcell, hbridge, lambdaCompute_eq_bool]

end ECCompute
