/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Defs
public import ECCompute.Soundness.RootMod

import ECCompute.ForLean

/-!
# Soundness of the column-legitimacy check

For a descent label `(p, θ)` the referee must verify, by exact integer arithmetic, the hypotheses
of the descent lemma packaged as `ECCompute.DescentHyp`:

* `p ∤ 6`     (so `p ≠ 2, 3`);
* `p ∤ Δ`     where `Δ` is the integer discriminant of `y² = x³ + a₂x² + a₄x + a₆`;
* `f(θ) ≡ 0 (mod p)`.

The kernel `Bool` checker `ECCompute.checkLabel` (defined in `ECCompute.Kernel`) decides all three;
`descentHyp_of_checkLabel` turns a passing `checkLabel` (with a separately supplied primality proof)
into a `DescentHyp`.

## Main declarations

* `ECCompute.descentHyp_of_checkLabel`: the passage from a passing `checkLabel` to `DescentHyp`.
* `ECCompute.checkLabels_true`: a passing `checkLabels` gives `checkLabel` for every label.
-/

namespace ECCompute

open WeierstrassCurve

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the case `a₁ = a₃ = 0`), matching
`WeierstrassCurve.Δ`. -/
def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ℤ}

/-- The rational discriminant of `curve a₂ a₄ a₆` is the integer `discrInt a₂ a₄ a₆`. -/
theorem curve_Δ_eq : (curve a₂ a₄ a₆).Δ = discrInt a₂ a₄ a₆ := by
  simp only [Δ, b₂, b₄, b₆, b₈, curve, discrInt]
  grind

/-- The numerator of the (integral) discriminant of `curve a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
theorem curve_Δ_num :
    (curve a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  rw [curve_Δ_eq, Rat.num_intCast]

/-- Reducing the coefficients mod `p` before `discrInt` gives the same value in `ZMod p`. -/
theorem discrInt_emod :
    (discrInt (a₂ % p) (a₄ % p) (a₆ % p) : ZMod p) = discrInt a₂ a₄ a₆ := by
  simp [discrInt]

/-- The label residue test reads as the monic cubic `θ³ + a₂θ² + a₄θ + a₆` vanishing mod `p`. -/
theorem fval_iff (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hp0 : p ≠ 0 := by lia
  have hpz : (p : ℤ) ≠ 0 := mod_cast hp0
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = (θ : ZMod p) := by
    rw [Int.emod_eq, Int.toNat_of_nonneg (Int.emod_nonneg θ hpz), ZMod.intCast_eq_intCast_iff']
    exact Int.emod_emod_of_dvd θ dvd_rfl
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by
    grind [polyEval]
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]

/-- `discrIntK a₂ a₄ a₆` equals the integer discriminant `discrInt a₂ a₄ a₆`. -/
theorem discrIntK_eq : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by
  grind [discrIntK, discrInt]

/-- If the kernel check passes and `p` is prime, the label `(p, ↑θ)` satisfies `DescentHyp`. -/
public theorem descentHyp_of_checkLabel
    (h : checkLabel a₂ a₄ a₆ p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  rw [checkLabel] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Bool.not'_eq_not] at h
  obtain ⟨h6, hΔ, hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_eq_mod]
    simpa [Nat.beq_eq_beq, beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    rw [curve_Δ_num, Ne, ← discrInt_emod, ← discrIntK_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq, ← Int.mod_def'] using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 :=
      (fval_iff hp.one_lt).mp hf
    rw [fval]
    grind

/-- If `checkLabels` passes, every label passes `checkLabel`. -/
public theorem checkLabels_true {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 := by
  rwa [checkLabels, allList_iff] at h

end ECCompute
