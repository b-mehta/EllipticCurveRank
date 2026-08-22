/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Kernel
import ECCompute.Soundness.Fold
import ECCompute.Soundness.IntResNat
import ECCompute.Soundness.RootMod
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

* `ECCompute.discrInt`: the integer discriminant of `curve a₂ a₄ a₆`.
* `ECCompute.curve_Δ_num`: `(curve …).Δ.num = discrInt …`.
* `ECCompute.descentHyp_of_checkLabel`: the passage to `DescentHyp`.
-/

namespace ECCompute

/-- The integer discriminant of `y² = x³ + a₂x² + a₄x + a₆` (the case `a₁ = a₃ = 0`), matching
`WeierstrassCurve.Δ`. -/
def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)

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
    (discrInt (a₂ % p) (a₄ % p) (a₆ % p) : ZMod p) = (discrInt a₂ a₄ a₆ : ZMod p) := by
  have h : ∀ a : ℤ, ((a % (p : ℤ)) : ZMod p) = (a : ZMod p) := fun a ↦ by
    rw [ZMod.intCast_eq_intCast_iff']; exact Int.emod_emod_of_dvd a dvd_rfl
  simp only [discrInt]
  push_cast [h]
  ring

/-- The label residue test reads as the monic cubic `θ³ + a₂θ² + a₄θ + a₆` vanishing mod `p`. -/
theorem fval_iff (a₂ a₄ a₆ θ : ℤ) {p : ℕ} (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by lia)
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = (θ : ZMod p) := by
    have hbridge : θ.emod (p : ℤ) = θ % (p : ℤ) := rfl
    rw [hbridge, Int.toNat_of_nonneg (Int.emod_nonneg θ hpz), ZMod.intCast_eq_intCast_iff']
    exact Int.emod_emod_of_dvd θ dvd_rfl
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by
    simp only [polyEval, Int.add_def, Int.mul_def]; ring
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]

/-- `discrIntK a₂ a₄ a₆` equals the integer discriminant `discrInt a₂ a₄ a₆`. -/
theorem discrIntK_eq (a₂ a₄ a₆ : ℤ) : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by
  simp only [discrIntK, discrInt, Int.mul_def, Int.add_def, Int.sub_eq, Int.neg_eq]
  ring

/-- If the kernel check passes and `p` is prime, the label `(p, ↑θ)` satisfies `DescentHyp`. -/
theorem descentHyp_of_checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ)
    (h : checkLabel a₂ a₄ a₆ p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  rw [checkLabel] at h
  obtain ⟨h6, hΔ, hf⟩ :
      (Nat.mod 6 p).beq 0 = false ∧
        ((discrIntK (a₂.emod p) (a₄.emod p) (a₆.emod p)).emod p).beq' 0 = false ∧
          (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0 := by grind
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    have h6m : 6 % p = Nat.mod 6 p := rfl
    rw [Nat.dvd_iff_mod_eq_zero, h6m]
    simpa [Nat.beq_eq', beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    rw [curve_Δ_num, Ne, ← discrInt_emod a₂ a₄ a₆ p, ← discrIntK_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq, ← Int.mod_def'] using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 :=
      (fval_iff a₂ a₄ a₆ θ hp.one_lt).mp hf
    rw [fval]
    grind

/-- If `checkLabels` passes, every label passes `checkLabel`. -/
theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 := by
  rwa [checkLabels, allList_eq_true] at h

end ECCompute
