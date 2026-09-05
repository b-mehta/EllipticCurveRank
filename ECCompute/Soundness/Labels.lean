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

The kernel `Bool` checker `ECCompute.checkLabel` (defined in `ECCompute.Kernel`) decides all
three from the coefficient residues and the discriminant carried in the certificate;
`descentHyp_of_checkLabel` turns a passing check (with a separately supplied primality proof)
into a `DescentHyp`.

## Main declarations

* `ECCompute.descentHyp_of_checkLabels`: a passing `checkLabels` gives `DescentHyp` for every label.
-/

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ℤ}

/-- The label residue test reads as the monic cubic `θ³ + a₂θ² + a₄θ + a₆` vanishing mod `p`. -/
theorem fval_iff (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hp0 : p ≠ 0 := by lia
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = θ := by
    rw [Int.cast_natCast]; exact intResNat_cast hp0
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by grind [polyEval]
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]

/-! ### The `Nat`-path label check gives the descent hypotheses -/

/-- `discrIntK a₂ a₄ a₆` equals the integer discriminant `discrInt a₂ a₄ a₆`. -/
theorem discrIntK_eq : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by grind [discrIntK, discrInt]

@[simp, grind =] theorem polyModK_cons {c : ℕ} {cs : List ℕ} {ℓ r : ℕ} :
    polyModK (c :: cs) ℓ r = (c % ℓ + r * polyModK cs ℓ r) % ℓ := rfl

/-- `polyModK` is `polyModL` on the coefficients cast to `ℤ`. -/
theorem polyModK_eq_polyModL {cs : List ℕ} {ℓ r : ℕ} :
    polyModK cs ℓ r = polyModL (cs.map Int.ofNat) ℓ r := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons]; grind [polyModL]

/-- A residue mod `P` reduces mod any divisor `p` of `P` to the coefficient itself in `ZMod p`. -/
theorem resP_cast {P : ℕ} {a : ℤ} (hP : P ≠ 0) (hpP : p ∣ P) {r : ℕ}
    (hr : r = (a % P).toNat) : (r % p : ZMod p) = a := by
  have hnn : 0 ≤ a % P := Int.emod_nonneg a (by exact mod_cast hP)
  rw [ZMod.natCast_mod, hr, ← Int.cast_natCast, Int.toNat_of_nonneg hnn,
    ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd a (by exact mod_cast hpP)

/-- A passing `checkLabel` (coefficient residues pinned mod `P`, `Δ` the discriminant) gives
`DescentHyp` for the label `(p, θ)`. -/
theorem descentHyp_of_checkLabel {P a₂r a₄r a₆r : ℕ} {Δ : ℤ} (hP : P ≠ 0) (hpP : p ∣ P)
    (h₂ : a₂r = (a₂ % P).toNat) (h₄ : a₄r = (a₄ % P).toNat) (h₆ : a₆r = (a₆ % P).toNat)
    (hΔ : Δ = discrInt a₂ a₄ a₆) (h : checkLabel a₂r a₄r a₆r Δ p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p θ := by
  have hp0 : 0 < p := hp.pos
  have hr₂' : (((a₂r % p : ℕ) : ℤ) : ZMod p) = a₂ := by
    simpa only [Int.cast_natCast] using resP_cast hP hpP h₂
  have hr₄' : (((a₄r % p : ℕ) : ℤ) : ZMod p) = a₄ := by
    simpa only [Int.cast_natCast] using resP_cast hP hpP h₄
  have hr₆' : (((a₆r % p : ℕ) : ℤ) : ZMod p) = a₆ := by
    simpa only [Int.cast_natCast] using resP_cast hP hpP h₆
  rw [checkLabel] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Bool.not'_eq_not, Nat.mod_eq_mod] at h
  obtain ⟨h6', hΔ', hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    grind [Nat.dvd_iff_mod_eq_zero]
  · -- `p ∤ Δ`: the discriminant is nonzero mod `p`
    rw [curveQ_Δ_num, Ne, ← hΔ, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq] using hΔ'
  · -- `f(θ) ≡ 0 (mod p)`: the `Nat` cubic residue vanishes
    grind [fval_iff, fval, polyModK_eq_polyModL, polyModL_beq]

/-- If `checkLabels` passes, every label satisfies `DescentHyp` (given its prime is prime). -/
public theorem descentHyp_of_checkLabels {labels : List (ℕ × ℤ)} {P a₂r a₄r a₆r : ℕ} {Δ : ℤ}
    (h : checkLabels a₂ a₄ a₆ P a₂r a₄r a₆r Δ labels) {l : ℕ × ℤ} (hl : l ∈ labels)
    (hp : l.1.Prime) : DescentHyp a₂ a₄ a₆ l.1 l.2 := by
  rw [checkLabels] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq, allList_iff, Nat.beq_eq,
    Int.beq'_eq] at h
  obtain ⟨hP, h₂, h₄, h₆, hΔ, hdvd, hfold⟩ := h
  rw [discrIntK_eq] at hΔ
  have hpd : P % l.1 = 0 := by grind
  exact descentHyp_of_checkLabel (by lia) (Nat.dvd_of_mod_eq_zero hpd) h₂ h₄ h₆ hΔ (hfold l hl) hp

end ECCompute
