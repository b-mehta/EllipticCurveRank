/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import ECCompute.Check.Fold
import ECCompute.Check.Primes
import ECCompute.Check.SignedNat
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

open scoped ECCompute.SN

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

/-- `discrInt` over signed-`Nat` pairs, so the kernel evaluates the discriminant in `Nat`. -/
noncomputable def discrIntSN (a₂ a₄ a₆ : ℤ) : ℕ × ℕ :=
  SN.neg ((SN.ofNat 4 *ₛ SN.ofInt a₂) ^ₛ 2
      *ₛ (SN.ofNat 4 *ₛ SN.ofInt a₂ *ₛ SN.ofInt a₆ -ₛ SN.ofInt a₄ ^ₛ 2))
    -ₛ SN.ofNat 8 *ₛ (SN.ofNat 2 *ₛ SN.ofInt a₄) ^ₛ 3
    -ₛ SN.ofNat 27 *ₛ (SN.ofNat 4 *ₛ SN.ofInt a₆) ^ₛ 2
    +ₛ SN.ofNat 9 *ₛ (SN.ofNat 4 *ₛ SN.ofInt a₂) *ₛ (SN.ofNat 2 *ₛ SN.ofInt a₄)
        *ₛ (SN.ofNat 4 *ₛ SN.ofInt a₆)

theorem discrIntSN_value (a₂ a₄ a₆ : ℤ) :
    SN.value (discrIntSN a₂ a₄ a₆) = discrInt a₂ a₄ a₆ := by
  simp only [discrIntSN, discrInt, SN.value_add, SN.value_sub, SN.value_neg, SN.value_mul,
    SN.value_pow, SN.value_ofInt, SN.value_ofNat, Nat.cast_ofNat]
  ring

/-- Reducing the coefficients mod `p` before `discrIntSN` gives the same value in `ZMod p` (so the
kernel builds the discriminant on small residues, not the full integer). -/
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
  haveI : NeZero p := ⟨hp.ne'⟩
  have hlt : fvalModP a₂ a₄ a₆ θ p < p := Nat.mod_lt _ hp
  have em : ∀ x y : ℕ, Nat.mod x y = x % y := fun _ _ => rfl
  have ea : ∀ x y : ℕ, Nat.add x y = x + y := fun _ _ => rfl
  have el : ∀ x y : ℕ, Nat.mul x y = x * y := fun _ _ => rfl
  have ei : ∀ z : ℤ, Int.emod z (p : ℤ) = z % (p : ℤ) := fun _ => rfl
  have hcast : ((fvalModP a₂ a₄ a₆ θ p : ℕ) : ZMod p)
      = ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) := by
    simp only [fvalModP, em, ea, el, ei, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
      SN.intResNat_cast hp]
    push_cast; ring
  have hnz : ((fvalModP a₂ a₄ a₆ θ p : ℕ) : ZMod p) = 0 ↔ fvalModP a₂ a₄ a₆ θ p = 0 := by
    rw [← ZMod.val_eq_zero, ZMod.val_cast_of_lt hlt]
  rw [Nat.beq_eq, ← hnz, hcast]

/-- Kernel-reducible check that the label `(p, θ)` satisfies the descent hypotheses `p ∤ 6`,
`p ∤ Δ`, and `f(θ) ≡ 0 (mod p)`, all in `Nat`. -/
noncomputable def checkLabel (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ℤ) : Bool :=
  ((Nat.beq (Nat.mod 6 p) 0).not').and'
    (((SN.dvd (discrIntSN (Int.emod a₂ p) (Int.emod a₄ p) (Int.emod a₆ p)) p).not').and'
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
    rw [Nat.dvd_iff_mod_eq_zero, show 6 % p = Nat.mod 6 p from rfl]
    simpa [← natBeqEq, beq_eq_false_iff_ne] using h6
  · -- `p ∤ Δ`
    have ei : ∀ z : ℤ, Int.emod z (p : ℤ) = z % (p : ℤ) := fun _ => rfl
    simp only [ei] at hΔ
    rw [curve_Δ_num, Ne, ← discrInt_emod a₂ a₄ a₆ p, ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← discrIntSN_value, ← SN.dvd_iff]
    simpa using hΔ
  · -- `f(θ) ≡ 0 (mod p)`
    have hcast : ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 :=
      (fvalModP_iff a₂ a₄ a₆ θ hp.pos).mp hf
    rw [fval]
    grind

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

/-- If `checkPrimes` passes, every label's prime component really is prime. -/
theorem checkPrimes_true {labels : List (ℕ × ℤ)} (h : checkPrimes labels = true) :
    ∀ l ∈ labels, (l.1).Prime := by
  rw [checkPrimes, allList_eq_true] at h
  exact fun l hl => checkPrime_true (h l hl)

/-- Kernel `Bool`: every label passes `checkLabel`. -/
noncomputable def checkLabels (a₂ a₄ a₆ : ℤ) (labels : List (ℕ × ℤ)) : Bool :=
  allList (fun l => checkLabel a₂ a₄ a₆ l.1 l.2) labels

/-- If `checkLabels` passes, every label passes `checkLabel`. -/
theorem checkLabels_true {a₂ a₄ a₆ : ℤ} {labels : List (ℕ × ℤ)}
    (h : checkLabels a₂ a₄ a₆ labels = true) :
    ∀ l ∈ labels, checkLabel a₂ a₄ a₆ l.1 l.2 = true := by
  rwa [checkLabels, allList_eq_true] at h

end ECCompute
