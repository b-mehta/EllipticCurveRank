/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Check.Fold
import ECCompute.Check.Primes
import Mathlib.Tactic.NormNum.Prime

/-!
# Column-legitimacy checks

For a descent label `(p, θ)` the referee must verify, by exact integer arithmetic, the hypotheses
of the descent lemma packaged as `ECCompute.DescentHyp`:

* `p ∤ 6`     (so `p ≠ 2, 3`);
* `p ∤ Δ`     where `Δ` is the integer discriminant of `y² = x³ + a₂x² + a₄x + a₆`;
* `f(θ) ≡ 0 (mod p)`.

`checkLabel` decides all three by `Int`/`Nat` `%` and `beq`, so a concrete instance closes by `rfl`;
`descentHyp_of_checkLabel` turns `checkLabel … = true` (with a separately supplied primality proof)
into a `DescentHyp`.

## Main declarations

* `ECCompute.discrInt`: the integer discriminant of `curve a₂ a₄ a₆`.
* `ECCompute.curve_Δ_num`: `(curve …).Δ.num = discrInt …`.
* `ECCompute.checkLabel`: the kernel-reducible boolean check.
* `ECCompute.descentHyp_of_checkLabel`: the passage to `DescentHyp`.
-/

open WeierstrassCurve

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
  push_cast
  ring

/-- The numerator of the (integral) discriminant of `curve a₂ a₄ a₆` is `discrInt a₂ a₄ a₆`. -/
theorem curve_Δ_num (a₂ a₄ a₆ : ℤ) :
    (curve a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  rw [curve_Δ_eq, Rat.num_intCast]

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`. -/
def checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ) : Bool :=
  (6 % p != 0) &&
  (discrInt a₂ a₄ a₆ % (p : ℤ) != 0) &&
  ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆) % (p : ℤ) == 0)

/-- If the kernel check passes and `p` is prime, the label `(p, ↑θ)` satisfies `DescentHyp`. -/
theorem descentHyp_of_checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ)
    (h : checkLabel a₂ a₄ a₆ p θ = true) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  rw [checkLabel, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h6, hΔ⟩, hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    rw [bne_iff_ne, ne_eq, ← Nat.dvd_iff_mod_eq_zero] at h6
    exact h6
  · -- `p ∤ Δ`
    rw [curve_Δ_num, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [bne_iff_ne, ne_eq, ← Int.dvd_iff_emod_eq_zero] at hΔ
    exact hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    rw [beq_iff_eq, ← Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    rw [fval]
    push_cast at hf ⊢
    linear_combination hf

/-! ### Worked example

A small standalone example: the short model `y² = x³ - x` (so `a₂ = 0, a₄ = -1, a₆ = 0`, with
integer discriminant `64`) and the label prime `p = 7`, root `θ = 1` (indeed `f(1) = 1 - 1 = 0`). -/

/-- The kernel check passes for the sample label, by `rfl` alone. -/
example : checkLabel 0 (-1) 0 7 1 = true := rfl

/-- Assembling a `DescentHyp` from the kernel check (`rfl`) and `norm_num` primality: the pattern
the certificate tactic emits for each column. -/
theorem example_descentHyp : DescentHyp 0 (-1) 0 7 ((1 : ℤ) : ZMod 7) :=
  descentHyp_of_checkLabel 0 (-1) 0 7 1 rfl (by norm_num)

/-- Kernel `Bool`: every label's prime component passes `checkPrime`. -/
noncomputable def checkPrimes (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkPrime l.1) labels

theorem checkPrimes_true {labels : List (ℕ × ℤ)} (h : checkPrimes labels = true) :
    ∀ l ∈ labels, (l.1).Prime := by
  rw [checkPrimes, allList_eq_true] at h
  exact fun l hl => checkPrime_true (h l hl)

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkLabel a₂ a₄ a₆ l.1 l.2) labels

theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels = true) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 = true := by
  rw [checkLabels, allList_eq_true] at h
  exact h

end ECCompute
