/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Soundness.Fold
import ECCompute.Check.Primes
import ECCompute.Check.IntResNat
import ECCompute.ForLean

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

/-- The label polynomial `f(θ) = θ³ + a₂θ² + a₄θ + a₆` reduced mod `p` in `Nat` (θ and the
coefficients reduced to residues first). -/
noncomputable def fvalModP (a₂ a₄ a₆ θ : ℤ) (p : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.add
    (Nat.mul (Nat.mul (Int.emod θ p).toNat (Int.emod θ p).toNat) (Int.emod θ p).toNat)
    (Nat.mul (Int.emod a₂ p).toNat (Nat.mul (Int.emod θ p).toNat (Int.emod θ p).toNat)))
    (Nat.mul (Int.emod a₄ p).toNat (Int.emod θ p).toNat)) (Int.emod a₆ p).toNat) p

theorem fvalModP_iff (a₂ a₄ a₆ θ : ℤ) {p : ℕ} (hp : 0 < p) :
    Nat.beq (fvalModP a₂ a₄ a₆ θ p) 0 = true
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have : NeZero p := ⟨hp.ne'⟩
  have hlt : fvalModP a₂ a₄ a₆ θ p < p := Nat.mod_lt _ hp
  have hcast : ((fvalModP a₂ a₄ a₆ θ p : ℕ) : ZMod p)
      = ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) := by
    simp only [fvalModP, Nat.mod_eq_mod, Nat.add_eq, Nat.mul_eq, ← Int.mod_def', ZMod.natCast_mod,
      Nat.cast_add, Nat.cast_mul, intResNat_cast hp.ne']
    push_cast
    ring
  rw [Nat.beq_eq, ← natCast_eq_zero_iff_of_lt hlt, hcast]

/-- `discrInt` written with the raw `Int.mul`/`Int.add`/`Int.sub`/`Int.neg` primitives, powers
expanded. -/
def discrIntK (a₂ a₄ a₆ : ℤ) : ℤ :=
  let b2 := Int.mul 4 a₂
  let b4 := Int.mul 2 a₄
  let b6 := Int.mul 4 a₆
  Int.add (Int.sub (Int.sub
      (Int.neg (Int.mul (Int.mul b2 b2)
        (Int.sub (Int.mul (Int.mul 4 a₂) a₆) (Int.mul a₄ a₄))))
      (Int.mul 8 (Int.mul (Int.mul b4 b4) b4)))
      (Int.mul 27 (Int.mul b6 b6)))
    (Int.mul (Int.mul (Int.mul 9 b2) b4) b6)

theorem discrIntK_eq (a₂ a₄ a₆ : ℤ) : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by
  simp only [discrIntK, discrInt, Int.mul_def, Int.add_def, Int.sub_eq, Int.neg_eq]
  ring

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ) : Bool :=
  ((Nat.beq (Nat.mod 6 p) 0).not').and'
    (((Int.beq' (Int.emod
      (discrIntK (Int.emod a₂ p) (Int.emod a₄ p) (Int.emod a₆ p)) p) 0).not').and'
      (Nat.beq (fvalModP a₂ a₄ a₆ θ p) 0))

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
    simpa [Nat.beq_eq', beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    rw [curve_Δ_num, Ne, ← discrInt_emod a₂ a₄ a₆ p, ← discrIntK_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq, ← Int.mod_def'] using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 :=
      (fvalModP_iff a₂ a₄ a₆ θ hp.pos).mp hf
    rw [fval]
    grind

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkLabel a₂ a₄ a₆ l.1 l.2) labels

/-- If `checkLabels` passes, every label passes `checkLabel`. -/
theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels = true) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 = true := by
  rwa [checkLabels, allList_eq_true] at h

end ECCompute
