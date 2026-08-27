/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Character
public import ECCompute.Soundness.RootMod

import Mathlib.Data.Nat.Bitwise
import ECCompute.ForLean

/-!
# Soundness of the kernel-reducible descent character

The kernel `Bool`/`Nat` builders that evaluate the descent character `λ_{p,θ}`
(`qrMask`, `qrLookupBool`, `lambdaK`, …) live in `ECCompute.Kernel`; this file
proves them correct.

## Main declarations

* `ECCompute.qrLookupBool_spec`: the mask bit test decides whether `a` is a nonzero square mod `p`.
* `ECCompute.lambdaK_eq`: the fully-`Nat` kernel mirror, read into `ZMod 2`,
  agrees with the abstract character `lambda`.
-/

namespace ECCompute

variable {p a : ℕ} {a₂ a₄ a₆ : ℤ}

/-! ### Quadratic-residue bitmask: kernel evaluation of the Legendre character

`qrMask` is the reference builder the certificate's supplied mask is checked against;
`qrLookupBool_spec` shows the bit test decides whether `a` is a nonzero square mod `p`.
-/

/-- The kernel bit test `(m >>> a) &&& 1 = 1` is `m.testBit a`. -/
theorem shiftRight_land_one_eq_one_iff {m : ℕ} : (m >>> a) &&& 1 = 1 ↔ m.testBit a := by
  grind [Nat.shiftRight_eq_div_pow]

/-- One-step unfolding of the quadratic-residue mask fold. -/
@[simp, grind =] theorem qrMaskGo_succ {k : ℕ} :
    qrMaskGo p (k + 1) = qrMaskGo p k ||| 1 <<< ((k + 1) * (k + 1) % p) := rfl

/-- Bit `a` of the fold is set iff some `1 ≤ j ≤ fuel` has `j² % p = a`. -/
@[grind =] theorem testBit_qrMaskGo {f : ℕ} :
    (qrMaskGo p f).testBit a ↔ ∃ j, 1 ≤ j ∧ j ≤ f ∧ j * j % p = a := by
  induction f with
  | zero => simp [qrMaskGo]
  | succ k ih =>
    rw [qrMaskGo_succ, Nat.testBit_lor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
      Bool.or_eq_true, ih, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj1, hjk, hja⟩ | hb)
      · exact ⟨j, by lia⟩
      · exact ⟨k + 1, by lia⟩
    · rintro ⟨j, hj1, hjk, hja⟩
      obtain h | rfl : j < k + 1 ∨ j = k + 1 := by lia
      · exact Or.inl ⟨j, by lia⟩
      · grind

/-- For `a < p`, `p` an odd prime: `a` is a residue witnessed in the lower half `[1, (p-1)/2]`
iff it is a nonzero square in `ZMod p`. -/
theorem exists_sq_iff (hp : p.Prime) (hp2 : p ≠ 2) (ha : a < p) :
    (∃ j, 1 ≤ j ∧ j ≤ (p - 1) / 2 ∧ j * j % p = a) ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  constructor
  · rintro ⟨j, hj1, hjk, hja⟩
    have hjp : j < p := by lia
    have hcast : (a : ZMod p) = j * j := by
      rw [← Nat.cast_mul, ← hja, ZMod.natCast_mod, Nat.cast_mul]
    refine ⟨?_, ⟨j, hcast⟩⟩
    rintro rfl
    exact (Nat.le_of_dvd (by lia) (by grind [hp.dvd_mul, Nat.dvd_of_mod_eq_zero hja])).not_gt hjp
  · rintro ⟨ha0, ⟨x, hx⟩⟩
    have hxne : x ≠ 0 := by
      rintro rfl
      exact ha0 (Nat.eq_zero_of_dvd_of_lt (by grind [ZMod.natCast_eq_zero_iff]) ha)
    have : NeZero p := ⟨by lia⟩
    wlog hx' : x.val ≤ (p - 1) / 2 generalizing x
    · exact this (-x) (by grind) (by grind) (by grind [ZMod.neg_val])
    have haeq : x.val * x.val % p = a := by
      have hc : (a : ZMod p) = (x.val * x.val : ℕ) := by rw [Nat.cast_mul, x.natCast_zmod_val, hx]
      grind [Nat.mod_eq_of_lt ha, ZMod.natCast_eq_natCast_iff']
    exact ⟨x.val, by grind [ZMod.val_eq_zero], hx', haeq⟩

/-- Bit `a` of `qrMask p` is set iff `a` is a nonzero square mod the odd prime `p` (for `a < p`). -/
theorem qrMask_testBit (hp2 : p ≠ 2) (hp : p.Prime) (ha : a < p) :
    qrMask p >>> a &&& 1 = 1 ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  rw [shiftRight_land_one_eq_one_iff, qrMask, testBit_qrMaskGo]
  exact exists_sq_iff hp hp2 ha

/-- The mask bit test decides whether `a` is a nonzero square mod `p` (for `a < p`, `p` an odd
prime). -/
theorem qrLookupBool_spec (hp2 : p ≠ 2) (hp : p.Prime) (ha : a < p) :
    qrLookupBool (qrMask p) a ↔ (a ≠ 0 ∧ IsSquare (a : ZMod p)) := by
  grind [qrLookupBool, qrMask_testBit]

variable {θ : ZMod p}

/-- For `p` an odd prime and `a ≠ 0`, reading the residue mask of `p` into `ZMod 2` gives the
abstract Legendre character `psi`. -/
theorem mask_eq_psi (hp : p.Prime) (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    (if qrLookupBool (qrMask p) a.val then 0 else 1) = psi p a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha0 : a.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  simp [qrLookupBool_spec hp2 hp (ZMod.val_lt a), ha0, psi]

/-! ### Fully `Nat` mirror

`lambdaK_eq` proves the kernel-reducible `Nat` builder `lambdaK`,
read into `ZMod 2`, agrees with the abstract character `lambda`. -/

section
variable {tval xp xm xden : ℕ}

/-- `alphaResNat` casts back to `x.num - θ·x.den` in `ZMod p`. -/
theorem alphaResNat_cast (hp : p ≠ 0) :
    (alphaResNat p tval xp xm xden : ZMod p) = xp - (xm + tval * xden) := by
  simp only [alphaResNat, Nat.mod_eq_mod, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ hp.bot_lt).le, ZMod.natCast_self, Nat.cast_mul]
  ring

/-- `alphaResNat` is the `ZMod p`-value of `x.num - θ·x.den`. -/
theorem alphaResNat_eq_val (hp : p ≠ 0) {x : ℚ}
    (htval : tval = θ) (hxnum : x.num = xp - xm) (hxden : xden = x.den) :
    alphaResNat p tval xp xm xden = (x.num - θ * x.den).val := by
  have hcast : (alphaResNat p tval xp xm xden : ZMod p) = x.num - θ * x.den := by
    rw [alphaResNat_cast hp, ← htval, ← hxden]
    have : (x.num : ZMod p) = xp - xm := by rw [hxnum]; push_cast; ring
    grind
  have hlt : alphaResNat p tval xp xm xden < p := Nat.mod_lt _ hp.bot_lt
  rw [← hcast, ZMod.val_cast_of_lt hlt]

/-- `fderivResNat` casts back to `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`. -/
theorem fderivResNat_cast (hp : p ≠ 0) (htval : tval = θ) :
    (fderivResNat a₂ a₄ p tval : ZMod p) = fderiv (a₂ : ZMod p) a₄ θ := by
  simp only [fderivResNat]
  rw [polyModL_cast hp]
  simp only [polyEval, Int.add_def, Int.mul_def]
  subst htval
  rw [fderiv]
  push_cast
  ring

/-- `fderivResNat` is the `ZMod p`-value of `f'(θ)`. -/
theorem fderivResNat_eq_val (hp : p ≠ 0) (htval : tval = θ) :
    fderivResNat a₂ a₄ p tval = (fderiv (a₂ : ZMod p) a₄ θ).val := by
  have hlt : fderivResNat a₂ a₄ p tval < p := by simp only [fderivResNat]; exact polyModL_lt hp
  rw [← fderivResNat_cast hp htval, ZMod.val_cast_of_lt hlt]

/-- `lambdaK` with the mask `qrMask p`, read into `ZMod 2`, equals the abstract
character `lambda` at the affine point, provided its `Nat` inputs encode the arguments: `θ = tval`,
and `x` has numerator `xp - xm` and denominator `xden`. -/
public theorem lambdaK_eq (hyp : DescentHyp a₂ a₄ a₆ p θ) {x y : ℚ}
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (htval : tval = θ) (hxnum : x.num = xp - xm) (hxden : xden = x.den) :
    (if lambdaK a₂ a₄ p (qrMask p) tval xp xm xden then 1 else 0)
      = lambda θ (.some x y h) := by
  have hp : p ≠ 0 := hyp.prime.ne_zero
  have hp2 : p ≠ 2 := fun hp ↦ hyp.ne_six (hp ▸ ⟨3, rfl⟩)
  have halpha := alphaResNat_eq_val hp htval hxnum hxden
  have hden : xden % p = 0 ↔ (x.den : ZMod p) = 0 := by
    rw [hxden, ← Nat.dvd_iff_mod_eq_zero, ZMod.natCast_eq_zero_iff]
  rw [lambdaK, lambda]
  grind [mask_eq_psi, hyp.prime, ZMod.val_eq_zero, fderivResNat_eq_val, fderiv_ne_zero]

end

end ECCompute
