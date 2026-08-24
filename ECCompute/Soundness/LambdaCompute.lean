/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.PsiBase
public import ECCompute.Soundness.RootMod

import Mathlib.Data.Nat.Bitwise
import ECCompute.ForLean

/-!
# Soundness of the kernel-reducible descent character

The descent character `λ_{p,θ}` (`ECCompute.Descent.Defs`) is `noncomputable`, as `ECCompute.psi`
decides `IsSquare` classically. To evaluate `λ` inside a certificate we need a `rfl`-reducible
replacement. For a fixed odd prime `p` we precompute, once per prime, a `Nat` bitmask `Q` whose bit
`a` is set exactly on the nonzero quadratic residues `a` mod `p`; each character evaluation is then
the bit test `((Q >>> a) &&& 1).beq 1`. The kernel `Bool`/`Nat` builders (`qrMask`, `qrLookupBool`,
`lambdaComputeBoolNatMask`, …) live in `ECCompute.Kernel`; this file proves them correct.

## Main declarations

* `ECCompute.lambdaCompute`: the `ZMod 2`-valued evaluation of `λ` on an affine point.
* `ECCompute.lambdaCompute_eq`: it agrees with the abstract `lambda`.
* `ECCompute.lambdaComputeBool`: the `Bool` mirror used by the certificate matrix checks.
* `ECCompute.lambdaCompute_eq_bool`: reads the `Bool` mirror back into `ZMod 2`.
* `ECCompute.lambdaComputeBoolNatMask_eq`: the fully-`Nat` kernel mirror agrees with
  `lambdaComputeBool`.
-/

namespace ECCompute

/-! ### Quadratic-residue bitmask: kernel evaluation of the Legendre character

For a fixed odd prime `p`, we precompute, once per prime, a `Nat` bitmask `Q` whose bit `a` is set
exactly on the nonzero quadratic residues `a` mod `p`. Each character evaluation is then the bit
test `((Q >>> a) &&& 1).beq 1`. `qrMask` is the reference builder the certificate's supplied mask
is checked against; `qrLookupBool_spec` shows the bit test decides whether `a` is a nonzero
square mod `p`.
-/

/-- The kernel bit test `(m >>> a) &&& 1 = 1` is `Nat.testBit m a`. -/
theorem shiftRight_land_one_eq_one_iff (m a : ℕ) :
    (m.shiftRight a).land 1 = 1 ↔ m.testBit a := by
  grind [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.land_eq]

/-- One-step unfolding of the quadratic-residue mask fold. -/
@[simp, grind =] theorem qrMaskGo_succ {p k : ℕ} :
    qrMaskGo p (k + 1) = (qrMaskGo p k).lor (Nat.shiftLeft 1 ((k.succ.mul k.succ).mod p)) := rfl

/-- Bit `a` of the fold is set iff some `1 ≤ j ≤ fuel` has `j² % p = a`. -/
theorem testBit_qrMaskGo (p a f : ℕ) :
    Nat.testBit (qrMaskGo p f) a ↔ ∃ j, 1 ≤ j ∧ j ≤ f ∧ j * j % p = a := by
  induction f with
  | zero =>
    simp only [qrMaskGo]
    constructor
    · rintro h; simp at h
    · rintro ⟨j, hj, hj0, _⟩; lia
  | succ k ih =>
    rw [qrMaskGo_succ, Nat.lor_eq, Nat.testBit_lor, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
      Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨j, hj1, hjk, hja⟩ | hb)
      · exact ⟨j, hj1, by lia, hja⟩
      · exact ⟨k + 1, by lia, by lia, of_decide_eq_true hb⟩
    · rintro ⟨j, hj1, hjk, hja⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hjk) with h | h
      · exact Or.inl ⟨j, hj1, by lia, hja⟩
      · subst h
        refine Or.inr ?_
        simp only [decide_eq_true_eq]
        exact hja

/-- For `0 < a < p`, `p` an odd prime: `a` is a residue witnessed in the lower half `[1, (p-1)/2]`
iff it is a nonzero square in `ZMod p`. -/
theorem exists_sq_iff (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    (∃ j, 1 ≤ j ∧ j ≤ (p - 1) / 2 ∧ j * j % p = a) ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  have hpp : p.Prime := hp.out
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp2
  have hp3 : 3 ≤ p := by have := hpp.two_le; lia
  constructor
  · rintro ⟨j, hj1, hjk, hja⟩
    have hjp : j < p := by lia
    have hcast : (a : ZMod p) = (j : ZMod p) * (j : ZMod p) := by
      rw [← Nat.cast_mul, ← hja, ZMod.natCast_mod, Nat.cast_mul]
    refine ⟨?_, ⟨(j : ZMod p), hcast⟩⟩
    intro h0
    rw [h0] at hja
    have hdvd : p ∣ j * j := Nat.dvd_of_mod_eq_zero hja
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with hd | hd <;>
      exact absurd (Nat.le_of_dvd (by lia) hd) (by lia)
  · rintro ⟨ha0, ⟨x, hx⟩⟩
    have hxne : x ≠ 0 := by
      rintro rfl
      apply ha0
      have hz : (a : ZMod p) = 0 := by rw [hx]; ring
      have := (ZMod.natCast_eq_zero_iff a p).mp hz
      exact Nat.eq_zero_of_dvd_of_lt this ha
    set v := x.val with hv
    have hv1 : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h | h
      · exact absurd (by rw [hv] at h; exact ZMod.val_eq_zero x |>.mp h) hxne
      · exact h
    have hvp : v < p := ZMod.val_lt x
    have hxcast : (v : ZMod p) = x := ZMod.natCast_zmod_val x
    have haeq : v * v % p = a := by
      have hc : (a : ZMod p) = ((v * v : ℕ) : ZMod p) := by
        rw [hx, Nat.cast_mul, hxcast]
      have hmod := (ZMod.natCast_eq_natCast_iff' a (v * v) p).mp hc
      rw [Nat.mod_eq_of_lt ha] at hmod
      lia
    by_cases hlow : v ≤ (p - 1) / 2
    · exact ⟨v, hv1, hlow, haeq⟩
    · refine ⟨p - v, by lia, by lia, ?_⟩
      have hsq : (p - v) * (p - v) % p = v * v % p := by
        have hkey : (((p - v) * (p - v) : ℕ) : ZMod p) = ((v * v : ℕ) : ZMod p) := by
          push_cast [Nat.cast_sub (by lia : v ≤ p)]
          ring_nf
          rw [ZMod.natCast_self]
          ring
        exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp hkey
      rw [hsq, haeq]

/-- Bit `a` of `qrMask p` is set iff `a` is a nonzero square mod the odd prime `p` (for `a < p`). -/
theorem qrMask_testBit (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    ((qrMask p).shiftRight a).land 1 = 1 ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  rw [shiftRight_land_one_eq_one_iff, qrMask, testBit_qrMaskGo]
  exact exists_sq_iff p hp2 a ha

/-- The mask bit test decides whether `a` is a nonzero square mod `p` (for `a < p`, `p` an odd
prime). This is what lets a verified mask evaluate the descent character at each call site. -/
theorem qrLookupBool_spec (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    qrLookupBool (qrMask p) a = decide (a ≠ 0 ∧ IsSquare (a : ZMod p)) := by
  have hmask := qrMask_testBit p hp2 a ha
  grind [qrLookupBool]

/-! ### `Bool` character and its `ZMod 2` lift -/

/-- `Bool`-valued evaluation of the descent character `λ_{p,θ}` on an affine point with
`x`-coordinate `x`, read from the quadratic-residue mask of `p`: `true` where `λ` is `1`, `false`
where it is `0`. -/
public noncomputable def lambdaComputeBool (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : Bool :=
  if (x.den : ZMod p) = 0 then false
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then
    !(qrLookupBool (qrMask p) (fderiv a₂ a₄ p θ).val)
  else !(qrLookupBool (qrMask p) ((x.num : ZMod p) - θ * (x.den : ZMod p)).val)

/-- The `ZMod 2`-valued evaluation of `λ_{p,θ}`: the `Bool` mirror `lambdaComputeBool` read into
`ZMod 2` (`true ↦ 1`, `false ↦ 0`). A certificate checks the character matrix over `Bool` and
recovers the `ZMod 2` value only at the end. -/
public noncomputable def lambdaCompute (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : ZMod 2 :=
  if lambdaComputeBool a₂ a₄ p θ x then 1 else 0

/-- `lambdaCompute` is `lambdaComputeBool` read into `ZMod 2`. -/
public theorem lambdaCompute_eq_bool (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) :
    lambdaCompute a₂ a₄ p θ x = if lambdaComputeBool a₂ a₄ p θ x then 1 else 0 := rfl

/-- For `p` an odd prime and `a ≠ 0`, reading the residue mask of `p` into `ZMod 2` gives the
abstract Legendre character `psi`. -/
private theorem mask_eq_psi (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    (if qrLookupBool (qrMask p) a.val then (0 : ZMod 2) else 1) = psi p a := by
  have hval' : (a.val : ZMod p) = a := ZMod.natCast_zmod_val a
  have hvlt : a.val < p := ZMod.val_lt a
  have ha0 : a.val ≠ 0 := fun h ↦ ha (by rw [← hval', h, Nat.cast_zero])
  have hspec := qrLookupBool_spec p hp2 a.val hvlt
  rw [hval'] at hspec
  rw [hspec]
  simp only [ne_eq, ha0, not_false_eq_true, true_and, psi]
  by_cases hsq : IsSquare a <;> simp [hsq]

/-- Under the descent hypotheses, `lambdaCompute` agrees with the abstract character `lambda` on
an affine point. -/
public theorem lambdaCompute_eq {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}
    (hyp : DescentHyp a₂ a₄ a₆ p θ) {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    lambdaCompute a₂ a₄ p θ x = lambda a₂ a₄ a₆ p θ (.some x y h) := by
  have : Fact p.Prime := ⟨hyp.prime⟩
  have hp2 : p ≠ 2 := fun hp ↦ hyp.ne_six (hp ▸ ⟨3, rfl⟩)
  have hfd : fderiv a₂ a₄ p θ ≠ 0 := fderiv_ne_zero hyp
  rw [lambdaCompute, lambdaComputeBool, lambda]
  grind [mask_eq_psi]

/-! ### Fully `Nat` mirror: signed inputs as `mp - mn` pairs

`lambdaComputeBool` casts the signed `x.num`, `a₂`, `a₄` into `ZMod p`. `lambdaComputeBoolNatMask`
does the same computation in `Nat`: each signed value arrives as a difference `mp - mn` of two `ℕ`,
the modulus reduction is `(mp % p + (p - mn % p)) % p`, and the characters are bit tests against the
quadratic-residue mask `qmask` of `p`. It agrees with `lambdaComputeBool` through
`lambdaComputeBoolNatMask_eq` (given `qmask = qrMask p`, `p` an odd prime, and that the pairs
represent the inputs). -/

/-- `alphaResNat` casts back to `x.num - θ·x.den` in `ZMod p`. -/
private theorem alphaResNat_cast {p : ℕ} (hp : 0 < p) (tval xp xm xden : ℕ) :
    (alphaResNat p tval xp xm xden : ZMod p)
      = (xp : ZMod p) - ((xm : ZMod p) + (tval : ZMod p) * (xden : ZMod p)) := by
  have hle : (xm + tval * xden) % p ≤ p := (Nat.mod_lt _ hp).le
  simp only [alphaResNat, Nat.mod_eq_mod, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub hle, ZMod.natCast_self, Nat.cast_mul]
  ring

/-- `alphaResNat` is the `ZMod p`-value of `x.num - θ·x.den`. -/
private theorem alphaResNat_eq_val {p : ℕ} (hp : 0 < p) (θ : ZMod p) (x : ℚ) (tval xp xm xden : ℕ)
    (htval : (tval : ZMod p) = θ) (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    alphaResNat p tval xp xm xden = ((x.num : ZMod p) - θ * (x.den : ZMod p)).val := by
  have hcast : (alphaResNat p tval xp xm xden : ZMod p)
      = (x.num : ZMod p) - θ * (x.den : ZMod p) := by
    rw [alphaResNat_cast hp, ← htval, ← hxden]
    have : (x.num : ZMod p) = (xp : ZMod p) - (xm : ZMod p) := by rw [hxnum]; push_cast; ring
    rw [this]; ring
  have hlt : alphaResNat p tval xp xm xden < p := Nat.mod_lt _ hp
  rw [← hcast, ZMod.val_cast_of_lt hlt]

/-- `fderivResNat` casts back to `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`. -/
private theorem fderivResNat_cast {p : ℕ} (hp : 0 < p) (a₂ a₄ : ℤ) (θ : ZMod p) (tval : ℕ)
    (htval : (tval : ZMod p) = θ) :
    (fderivResNat a₂ a₄ p tval : ZMod p) = fderiv a₂ a₄ p θ := by
  simp only [fderivResNat]
  rw [polyModL_cast hp.ne']
  simp only [polyEval, Int.add_def, Int.mul_def]
  subst htval
  unfold fderiv
  push_cast
  ring

/-- `fderivResNat` is the `ZMod p`-value of `f'(θ)`. -/
private theorem fderivResNat_eq_val {p : ℕ} (hp : 0 < p) (a₂ a₄ : ℤ) (θ : ZMod p) (tval : ℕ)
    (htval : (tval : ZMod p) = θ) :
    fderivResNat a₂ a₄ p tval = (fderiv a₂ a₄ p θ).val := by
  have hlt : fderivResNat a₂ a₄ p tval < p := by
    simp only [fderivResNat]; exact polyModL_lt hp
  rw [← fderivResNat_cast hp a₂ a₄ θ tval htval, ZMod.val_cast_of_lt hlt]

/-- `lambdaComputeBoolNatMask` with the mask `qrMask p` equals the abstract `lambdaComputeBool`,
provided its `Nat` inputs encode the arguments: `θ = tval`, and `x` has numerator `xp - xm` and
denominator `xden`. -/
public theorem lambdaComputeBoolNatMask_eq (a₂ a₄ : ℤ) (p : ℕ) (hp : 0 < p) (θ : ZMod p) (x : ℚ)
    (tval xp xm xden : ℕ) (htval : (tval : ZMod p) = θ)
    (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    lambdaComputeBoolNatMask a₂ a₄ p (qrMask p) tval xp xm xden
      = lambdaComputeBool a₂ a₄ p θ x := by
  have halpha := alphaResNat_eq_val hp θ x tval xp xm xden htval hxnum hxden
  have hfd := fderivResNat_eq_val hp a₂ a₄ θ tval htval
  have hden : (xden.mod p = 0) = ((x.den : ZMod p) = 0) := by
    rw [hxden, Nat.mod_eq_mod, ← Nat.dvd_iff_mod_eq_zero, eq_iff_iff, ZMod.natCast_eq_zero_iff]
  rw [lambdaComputeBool, lambdaComputeBoolNatMask]
  simp only [Bool.rec_eq, Nat.beq_eq, Bool.not'_eq_not, halpha, hfd, hden, ZMod.val_eq_zero]

end ECCompute
