/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Check.Labels
import ECCompute.Theory.Descent.Defs

/-!
# Soundness of the column-legitimacy checks

`descentHyp_of_checkLabel` turns `checkLabel … = true` (with a separately supplied primality proof)
into a `DescentHyp`; `checkLabels_true` lifts it to a list. Along the way `curve_Δ_num`,
`discrInt_emod`, `discrIntK_eq` and `fvalModP_iff` relate the kernel checks (from `Check.Labels`) to
the discriminant and label polynomial over `ZMod p`.
-/

open WeierstrassCurve

namespace ECCompute

/-- The rational discriminant of `curve a₂ a₄ a₆` is the integer `discrInt a₂ a₄ a₆`. -/
theorem curve_Δ_eq (a₂ a₄ a₆ : ℤ) :
    (curve a₂ a₄ a₆).Δ = (discrInt a₂ a₄ a₆ : ℚ) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve, discrInt]
  grind

/-- The numerator of the (integral) discriminant of `curve a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
theorem curve_Δ_num (a₂ a₄ a₆ : ℤ) :
    (curve a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  rw [curve_Δ_eq, Rat.num_intCast]

/-- Reducing the coefficients mod `p` before `discrInt` gives the same value in `ZMod p`. -/
theorem discrInt_emod (a₂ a₄ a₆ : ℤ) (p : ℕ) :
    ((discrInt (a₂ % p) (a₄ % p) (a₆ % p) : ℤ) : ZMod p) = (discrInt a₂ a₄ a₆ : ZMod p) := by
  have h : ∀ a : ℤ, ((a % (p : ℤ) : ℤ) : ZMod p) = (a : ZMod p) := fun a => by
    rw [ZMod.intCast_eq_intCast_iff']; exact Int.emod_emod_of_dvd a dvd_rfl
  simp only [discrInt]
  push_cast [h]
  ring

/-- The mod-`p` `Nat` test `fvalModP` is zero exactly when `f(θ)` vanishes in `ZMod p` (`0 < p`). -/
theorem fvalModP_iff (a₂ a₄ a₆ θ : ℤ) {p : ℕ} (hp : 0 < p) :
    Nat.beq (fvalModP a₂ a₄ a₆ θ p) 0 = true
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have : NeZero p := ⟨hp.ne'⟩
  have hlt : fvalModP a₂ a₄ a₆ θ p < p := Nat.mod_lt _ hp
  have hcast : ((fvalModP a₂ a₄ a₆ θ p : ℕ) : ZMod p)
      = ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) := by
    simp only [fvalModP, Nat.mod_eq_mod, Nat.add_eq, Nat.mul_eq, ← Int.mod_def', ZMod.natCast_mod,
      Nat.cast_add, Nat.cast_mul, intResNat_cast]
    push_cast
    ring
  rw [Nat.beq_eq, ← natCast_eq_zero_iff_of_lt hlt, hcast]

/-- `discrIntK` computes `discrInt`. -/
theorem discrIntK_eq (a₂ a₄ a₆ : ℤ) : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by
  simp only [discrIntK, discrInt, Int.mul_def, Int.add_def, Int.sub_eq, Int.neg_eq]
  ring

/-- If the kernel check passes and `p` is prime, the label `(p, ↑θ)` satisfies `DescentHyp`. -/
theorem descentHyp_of_checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ)
    (h : checkLabel a₂ a₄ a₆ p θ = true) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  rw [checkLabel] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Bool.not'_eq_not] at h
  obtain ⟨h6, hΔ, hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    have h6m : 6 % p = Nat.mod 6 p := rfl
    rw [Nat.dvd_iff_mod_eq_zero, h6m]
    simpa [← natBeqEq, beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    rw [curve_Δ_num, Ne, ← discrInt_emod a₂ a₄ a₆ p, ← discrIntK_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq, ← Int.mod_def'] using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 :=
      (fvalModP_iff a₂ a₄ a₆ θ hp.pos).mp hf
    rw [fval]
    grind

/-- If `checkLabels` passes, every label passes `checkLabel`. -/
theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels = true) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 = true := by
  rwa [checkLabels, allList_eq_true] at h

end ECCompute
