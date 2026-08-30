/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character
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

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ℤ}

/-- Reducing the coefficients mod `p` before `discrInt` gives the same value in `ZMod p`. -/
theorem discrInt_emod : (discrInt (a₂ % p) (a₄ % p) (a₆ % p) : ZMod p) = discrInt a₂ a₄ a₆ := by
  simp [discrInt]

/-- The label residue test reads as the monic cubic `θ³ + a₂θ² + a₄θ + a₆` vanishing mod `p`. -/
theorem fval_iff (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hp0 : p ≠ 0 := by lia
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = (θ : ZMod p) := by
    rw [Int.cast_natCast]; exact intResNat_cast hp0
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by grind [polyEval]
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]

/-- `discrIntK a₂ a₄ a₆` equals the integer discriminant `discrInt a₂ a₄ a₆`. -/
theorem discrIntK_eq : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by grind [discrIntK, discrInt]

/-- If the kernel check passes and `p` is prime, the label `(p, ↑θ)` satisfies `DescentHyp`. -/
public theorem descentHyp_of_checkLabel (h : checkLabel a₂ a₄ a₆ p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  rw [checkLabel] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Bool.not'_eq_not] at h
  obtain ⟨h6, hΔ, hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_eq_mod]
    simpa [Nat.beq_eq_beq, beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    rw [curveQ_Δ_num, Ne, ← discrInt_emod, ← discrIntK_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq, ← Int.mod_def'] using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := (fval_iff hp.one_lt).mp hf
    rw [fval]
    grind

/-! ### The `Nat`-path label check reduces to `checkLabel`

`checkLabels` reduces the big coefficients modulo the label-prime product `P` once, records the
residues as `Nat` literals `a2r, a4r, a6r`, and runs each label's check in `Nat` (`checkLabelNat`).
The lemmas below cast the `Nat` discriminant and cubic back into `ZMod p` and match them with
`checkLabel`. -/

/-- `subModP` casts to a subtraction in `ZMod p` once the subtrahend is a residue mod `p`. -/
theorem subModP_cast {x z : ℕ} (hp : 0 < p) :
    (subModP p x (z % p) : ZMod p) = (x : ZMod p) - z := by
  have hle : z % p ≤ p := (Nat.mod_lt z hp).le
  rw [subModP, Nat.mod_eq_mod, ZMod.natCast_mod, Nat.add_eq, Nat.cast_add,
    show p.sub (z % p) = p - z % p from rfl, Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- The `Nat` discriminant `discrModP` casts to the integer discriminant of its residues. -/
theorem discrModP_cast (hp : 0 < p) {rp2 rp4 rp6 : ℕ} :
    (discrModP rp2 rp4 rp6 p : ZMod p) = discrInt rp2 rp4 rp6 := by
  simp only [discrModP, Nat.mod_eq_mod, Nat.mul_eq]
  push_cast [ZMod.natCast_mod, subModP_cast hp]
  simp only [discrInt]
  push_cast
  ring

/-- Casting the integer discriminant through agreeing residues in `ZMod p`. -/
theorem discrInt_zmod_congr {X Y Z : ℤ} (hx : (X : ZMod p) = a₂) (hy : (Y : ZMod p) = a₄)
    (hz : (Z : ZMod p) = a₆) : (discrInt X Y Z : ZMod p) = discrInt a₂ a₄ a₆ := by
  simp only [discrInt]
  push_cast
  rw [hx, hy, hz]

/-- The `Nat` cubic `cubicModP` casts to the monic cubic `polyEval [a₆, a₄, a₂, 1]` in `ZMod p`. -/
theorem cubicModP_cast {rp2 rp4 rp6 t : ℕ} :
    (cubicModP rp2 rp4 rp6 p t : ZMod p) =
      (rp6 : ZMod p) + t * (rp4 + t * (rp2 + t)) := by
  simp only [cubicModP, Nat.mod_eq_mod, Nat.add_eq, Nat.mul_eq]
  push_cast [ZMod.natCast_mod]
  ring

/-- A residue mod the label-prime product `P` reduces mod any divisor `p` of `P` to the coefficient
itself in `ZMod p`. -/
theorem resP_cast {P : ℕ} {a : ℤ} (hP : 0 < P) (hpP : p ∣ P) {r : ℕ}
    (hr : r = (a % (P : ℤ)).toNat) : ((r % p : ℕ) : ZMod p) = (a : ZMod p) := by
  have hnn : 0 ≤ a % (P : ℤ) := Int.emod_nonneg a (by exact_mod_cast hP.ne')
  rw [ZMod.natCast_mod, hr, ← Int.cast_natCast, Int.toNat_of_nonneg hnn,
    ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd a (by exact_mod_cast hpP)

/-- A `Nat` residue `n < p` vanishes iff it vanishes in `ZMod p`. -/
theorem natCast_eq_zero_of_lt {n : ℕ} (hn : n < p) : (n = 0) ↔ ((n : ZMod p) = 0) := by
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hn]

/-- The per-label passage: a passing `Nat`-path `checkLabelNat` on residues pinned to `a₂, a₄, a₆`
mod `P` and the discriminant residue `dr = Δ mod P` (with `p ∣ P` and `0 < P`) gives a passing
`checkLabel`.

MEASUREMENT-ONLY: soundness with the shared `dr` literal is not yet reproved. -/
theorem checkLabel_of_checkLabelNat {P a2r a4r a6r dr : ℕ} (hP : 0 < P) (hpP : p ∣ P)
    (h2 : a2r = (a₂ % (P : ℤ)).toNat) (h4 : a4r = (a₄ % (P : ℤ)).toNat)
    (h6 : a6r = (a₆ % (P : ℤ)).toNat) (hdr : (discrModP a2r a4r a6r P).beq dr)
    (h : checkLabelNat a2r a4r a6r dr p θ) :
    checkLabel a₂ a₄ a₆ p θ := by
  sorry

/-- If `checkLabels` passes, every label passes `checkLabel`. The `Nat`-path `checkLabels` verifies
the emitted residue literals against `a₂, a₄, a₆ mod P` and the discriminant residue `dr` against
`Δ mod P`, then runs the per-label check in `Nat`; `checkLabel_of_checkLabelNat` carries each label
back to the `Int`-path `checkLabel`.

MEASUREMENT-ONLY: soundness with the shared `dr` literal is not yet reproved. -/
public theorem checkLabels_true {labels : List (ℕ × ℤ)} {P a2r a4r a6r dr : ℕ}
    (h : checkLabels a₂ a₄ a₆ P a2r a4r a6r dr labels) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 := by
  sorry

end ECCompute
