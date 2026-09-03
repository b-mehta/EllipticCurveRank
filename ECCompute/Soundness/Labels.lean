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
three in `Nat` on the coefficient residues carried in the certificate;
`descentHyp_of_checkLabel` turns a passing check (with a separately supplied primality proof)
into a `DescentHyp`.

## Main declarations

* `ECCompute.descentHyp_of_checkLabel`: a passing `checkLabel` gives `DescentHyp`.
* `ECCompute.descentHyp_of_checkLabels`: a passing `checkLabels` gives `DescentHyp` for every label.
-/

namespace ECCompute

open WeierstrassCurve

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ℤ}

/-- The label residue test reads as the monic cubic `θ³ + a₂θ² + a₄θ + a₆` vanishing mod `p`. -/
theorem fval_iff (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hp0 : p ≠ 0 := by lia
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = (θ : ZMod p) := by
    rw [Int.cast_natCast]; exact intResNat_cast hp0
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by grind [polyEval]
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]

/-! ### The `Nat`-path label check gives the descent hypotheses

`checkLabels` reduces the big coefficients modulo the label-prime product `P` once, records the
residues as `Nat` literals `a₂r, a₄r, a₆r`, and runs each label's check in `Nat` (`checkLabel`).
The lemmas below cast the `Nat` discriminant and cubic into `ZMod p` and read off `DescentHyp`. -/

/-- `subModK` casts to a subtraction in `ZMod p` once the subtrahend is a residue mod `p`. -/
theorem subModK_cast {x z : ℕ} (hp : p ≠ 0) :
    (subModK p x (z % p) : ZMod p) = (x : ZMod p) - z := by
  have hsub : p.sub (z % p) = p - z % p := rfl
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  rw [subModK, Nat.mod_eq_mod, ZMod.natCast_mod, Nat.add_eq, Nat.cast_add,
    hsub, Nat.cast_sub (Nat.mod_lt z hp0).le, ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- The `Nat` discriminant `discrModK` casts to the integer discriminant of its residues. -/
theorem discrModK_cast (hp : p ≠ 0) {rp2 rp4 rp6 : ℕ} :
    (discrModK rp2 rp4 rp6 p : ZMod p) = discrInt rp2 rp4 rp6 := by
  simp only [discrModK, Nat.mod_eq_mod, Nat.mul_eq, Nat.add_eq, discrInt]
  push_cast [ZMod.natCast_mod, subModK_cast hp]
  ring

/-- Casting the integer discriminant through agreeing residues in `ZMod p`. -/
theorem discrInt_zmod_congr {X Y Z : ℤ} (hx : (X : ZMod p) = a₂) (hy : (Y : ZMod p) = a₄)
    (hz : (Z : ZMod p) = a₆) : (discrInt X Y Z : ZMod p) = discrInt a₂ a₄ a₆ := by
  simp only [discrInt]
  push_cast
  rw [hx, hy, hz]

@[simp, grind =] theorem polyModK_cons {c : ℕ} {cs : List ℕ} {ℓ r : ℕ} :
    polyModK (c :: cs) ℓ r = ((c % ℓ) + r * polyModK cs ℓ r) % ℓ := by simp [polyModK]

/-- `polyModK` is `polyModL` on the coefficients cast to `ℤ`. -/
theorem polyModK_eq_polyModL {cs : List ℕ} {ℓ r : ℕ} :
    polyModK cs ℓ r = polyModL (cs.map Int.ofNat) ℓ r := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons]
    grind [polyModL]

/-- A residue mod the label-prime product `P` reduces mod any divisor `p` of `P` to the coefficient
itself in `ZMod p`. -/
theorem resP_cast {P : ℕ} {a : ℤ} (hP : P ≠ 0) (hpP : p ∣ P) {r : ℕ}
    (hr : r = (a % (P : ℤ)).toNat) : ((r % p : ℕ) : ZMod p) = (a : ZMod p) := by
  have hnn : 0 ≤ a % (P : ℤ) := Int.emod_nonneg a (by exact mod_cast hP)
  rw [ZMod.natCast_mod, hr, ← Int.cast_natCast, Int.toNat_of_nonneg hnn,
    ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd a (by exact mod_cast hpP)

/-- A `Nat` residue `n < p` vanishes iff it vanishes in `ZMod p`. -/
theorem natCast_eq_zero_of_lt {n : ℕ} (hn : n < p) : (n = 0) ↔ ((n : ZMod p) = 0) := by
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hn]

/-- A passing `Nat`-path `checkLabel` on residues pinned to `a₂, a₄, a₆` mod `P` (with `p ∣ P`,
`P ≠ 0`, and `p` prime) gives `DescentHyp` for the label `(p, θ)`. -/
theorem descentHyp_of_checkLabel {P a₂r a₄r a₆r : ℕ} (hP : P ≠ 0) (hpP : p ∣ P)
    (h2 : a₂r = (a₂ % (P : ℤ)).toNat) (h4 : a₄r = (a₄ % (P : ℤ)).toNat)
    (h6 : a₆r = (a₆ % (P : ℤ)).toNat) (h : checkLabel a₂r a₄r a₆r p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p (θ : ZMod p) := by
  have hp0 : 0 < p := hp.pos
  have hr2 : ((a₂r % p : ℕ) : ZMod p) = a₂ := resP_cast hP hpP h2
  have hr4 : ((a₄r % p : ℕ) : ZMod p) = a₄ := resP_cast hP hpP h4
  have hr6 : ((a₆r % p : ℕ) : ZMod p) = a₆ := resP_cast hP hpP h6
  have hr2' : (((a₂r % p : ℕ) : ℤ) : ZMod p) = a₂ := by rw [Int.cast_natCast]; exact hr2
  have hr4' : (((a₄r % p : ℕ) : ℤ) : ZMod p) = a₄ := by rw [Int.cast_natCast]; exact hr4
  have hr6' : (((a₆r % p : ℕ) : ℤ) : ZMod p) = a₆ := by rw [Int.cast_natCast]; exact hr6
  rw [checkLabel] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Bool.not'_eq_not, Nat.mod_eq_mod] at h
  obtain ⟨h6', hΔ, hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · -- `p ∤ 6`
    grind [Nat.dvd_iff_mod_eq_zero]
  · -- `p ∤ Δ`: the `Nat` discriminant is nonzero, hence so is `Δ.num` in `ZMod p`
    rw [curveQ_Δ_num, Ne, ← discrInt_zmod_congr hr2' hr4' hr6', ← discrModK_cast hp0.ne',
      ← natCast_eq_zero_of_lt (by rw [discrModK]; exact Nat.mod_lt _ hp0)]
    grind
  · -- `f(θ) ≡ 0 (mod p)`: the `Nat` cubic residue vanishes
    grind [fval_iff, fval, polyModK_eq_polyModL, polyModL_beq]

/-- If `checkLabels` passes, every label satisfies `DescentHyp` (given its prime is prime). The
`Nat`-path `checkLabels` verifies the emitted residue literals against `a₂, a₄, a₆ mod P` and runs
the per-label check in `Nat`; `descentHyp_of_checkLabel` carries each label to `DescentHyp`. -/
public theorem descentHyp_of_checkLabels {labels : List (ℕ × ℤ)} {P a₂r a₄r a₆r : ℕ}
    (h : checkLabels a₂ a₄ a₆ P a₂r a₄r a₆r labels) {l : ℕ × ℤ} (hl : l ∈ labels)
    (hp : l.1.Prime) : DescentHyp a₂ a₄ a₆ l.1 (l.2 : ZMod l.1) := by
  rw [checkLabels] at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨hP, h2, h4, h6, hdvd, hfold⟩ := h
  rw [Nat.ble_eq] at hP
  rw [allList_iff] at hdvd hfold
  simp only [Nat.beq_eq_beq, beq_iff_eq] at h2 h4 h6
  have hpd : P % l.1 = 0 := by have := hdvd l hl; grind
  exact descentHyp_of_checkLabel (by lia) (Nat.dvd_of_mod_eq_zero hpd) h2 h4 h6 (hfold l hl) hp

end ECCompute
