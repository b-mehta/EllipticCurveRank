/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Soundness
import ECCompute.ModelChange
import ECCompute.CheckMatrix
import ECCompute.QuickRfl
import ECCompute.Primes
import Mathlib.Tactic.NormNum.Prime

/-!
# The front door for a rank certificate

`ECCompute.Soundness.rank_ge_of_certificate` proves a rank lower bound on the *short integral model*
`curve c.a₂ c.a₄ c.a₆`, where the descent character lives.  A concrete curve is usually given by a
*general* integral Weierstrass model `toCurveQ a₁ a₂ a₃ a₄ a₆`; `ModelChange.generalToShortEquiv`
carries it to the short model `intShortModel a₁ a₂ a₃ a₄ a₆` by completing the square and scaling.

`hasRankGE_of_certificate` bolts these two together, so each instantiation only has to supply the
certificate data, the six referee facts, and the single equation identifying the certificate's short
model with the target of the change of variables.  It replaces the roughly ten-line "unfold,
assemble, transport" tail that every curve file would otherwise repeat.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- `l.getD n d` is a genuine member of `l` when the index is in range. -/
private theorem getD_mem_of_lt {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- Kernel `Bool`: `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`ECCompute.passes`).  Every descent-label prime used by the rank certificates is `< 529`. -/
noncomputable def checkPrime (p : ℕ) : Bool :=
  (Nat.ble 2 p).and' ((Nat.ble p 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

theorem checkPrime_true {p : ℕ} (h : checkPrime p = true) : p.Prime := by
  simp only [checkPrime, Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, hle, hpass⟩ := h
  exact Nat.prime_of_passes p h2 (by omega) hpass

/-- Kernel `Bool`: every label's prime component passes `checkPrime`.  A structural `allList` fold
over the label `List`, so the kernel never applies a `Fin _ → _` family nor indexes positionally. -/
noncomputable def checkPrimes (labels : List (ℕ × ℤ)) : Bool :=
  F2Invert.allList (fun l => checkPrime l.1) labels

theorem checkPrimes_true {labels : List (ℕ × ℤ)} (h : checkPrimes labels = true) :
    ∀ l ∈ labels, (l.1).Prime := by
  rw [checkPrimes, F2Invert.allList_eq_true] at h
  exact fun l hl => checkPrime_true (h l hl)

/-- Kernel `Bool`: every label passes `checkLabel`.  A structural `allList` fold over the label
`List`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  F2Invert.allList (fun l => checkLabel a₂ a₄ a₆ l.1 l.2) labels

theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels = true) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 = true := by
  rw [checkLabels, F2Invert.allList_eq_true] at h
  exact h

/-- **The certified rank lower bound for a general integral model.**  Given a certificate `c` whose
short model `curve c.a₂ c.a₄ c.a₆` is the change-of-variables target of the general model
`toCurveQ a₁ a₂ a₃ a₄ a₆` (the equation `hmodel`), and the six referee facts of
`rank_ge_of_certificate`, the Mordell–Weil rank of `toCurveQ a₁ a₂ a₃ a₄ a₆` over `ℚ` is at least
`c.rho - c.t`.  The bound is proven on the short model and transported along
`generalToShortEquiv`. -/
theorem hasRankGE_of_certificate (a₁ a₂ a₃ a₄ a₆ : ℤ) (c : Certificate)
    (hmodel : intShortModel a₁ a₂ a₃ a₄ a₆ = curve c.a₂ c.a₄ c.a₆)
    (hlenP : c.points.length = c.rho)
    (hlenL : c.labels.length = c.rho)
    (hpt : checkPoints 0 c.a₂ 0 c.a₄ c.a₆ c.points = true)
    (hlabP : checkPrimes c.labels = true)
    (hlabC : checkLabels c.a₂ c.a₄ c.a₆ c.labels = true)
    (hB : checkB c.a₂ c.a₄ c.a₆ c.matB c.rho c.labels c.points = true)
    (hinv : F2Invert.checkInv c.rho c.matB c.matM = true)
    (ht : c.t = 0)
    (htorP : c.torsionPrime ≠ 0)
    (htor : hasRootMod (4 * c.a₂) (16 * c.a₄) (64 * c.a₆) c.torsionPrime = false) :
    HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) (c.rho - c.t) := by
  -- The point/label families the soundness theorem consumes are read from the certificate's lists
  -- by `getD`.  Every kernel-checked hypothesis above is `List`-based, so the kernel never reduces
  -- a `Fin c.rho → _` function; the families here appear only in the (non-computational) proof.
  have hmemP : ∀ i : Fin c.rho, c.points.getD i.val (0, 0) ∈ c.points :=
    fun i => getD_mem_of_lt (by rw [hlenP]; exact i.isLt)
  have hmemL : ∀ j : Fin c.rho, c.labels.getD j.val (0, 0) ∈ c.labels :=
    fun j => getD_mem_of_lt (by rw [hlenL]; exact j.isLt)
  have hcurve : curve c.a₂ c.a₄ c.a₆ = toCurveQ 0 c.a₂ 0 c.a₄ c.a₆ := by
    simp only [curve, toCurveQ, Int.cast_zero]
  rw [checkPoints_iff] at hpt
  have hpt' : ∀ i : Fin c.rho, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation
      (c.points.getD i.val (0, 0)).1 (c.points.getD i.val (0, 0)).2 := by
    intro i
    rw [hcurve]
    exact hpt _ (hmemP i)
  have hlabP' : ∀ j : Fin c.rho, ((c.labels.getD j.val (0, 0)).1).Prime :=
    fun j => checkPrimes_true hlabP _ (hmemL j)
  have hlabC' : ∀ j : Fin c.rho, checkLabel c.a₂ c.a₄ c.a₆
      (c.labels.getD j.val (0, 0)).1 (c.labels.getD j.val (0, 0)).2 = true :=
    fun j => checkLabels_true hlabC _ (hmemL j)
  have key : HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) :=
    rank_ge_of_certificate c (fun i => c.points.getD i.val (0, 0))
      (fun j => c.labels.getD j.val (0, 0)) hpt' hlabP' hlabC' (checkB_true hB) hinv ht htorP htor
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
