/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.PsiBase
import ECCompute.Check.IntResNat
import Mathlib.Data.Nat.Bitwise

/-!
# A kernel-reducible descent character

The descent character `λ_{p,θ}` (`ECCompute.Descent.Defs`) is `noncomputable`, as `ECCompute.psi`
decides `IsSquare` classically. To evaluate `λ` inside a certificate we need a `rfl`-reducible
replacement. For a fixed odd prime `p` we precompute, once per prime, a `Nat` bitmask `Q` whose bit
`a` is set exactly on the nonzero quadratic residues `a` mod `p`; each character evaluation is then
the bit test `((Q >>> a) &&& 1).beq 1`.

## Main declarations

* `ECCompute.qrMask`: reference quadratic-residue-mask builder for a prime `p`.
* `ECCompute.qrLookupBool`: the bit test against a supplied mask.
* `ECCompute.qrLookupBool_spec`: the bit test decides `a ≠ 0 ∧ IsSquare (a : ZMod p)`.
* `ECCompute.psiCompute`: kernel-reducible replacement for `psi`.
* `ECCompute.psiCompute_eq`: `psiCompute p a = psi p a` (`p` odd prime, `a ≠ 0`).
* `ECCompute.lambdaCompute`: kernel-reducible evaluation of `λ` on an affine point.
* `ECCompute.lambdaCompute_eq`: it agrees with the abstract `lambda`.
-/

namespace ECCompute

/-! ### Quadratic-residue bitmask: kernel evaluation of the Legendre character

For a fixed odd prime `p`, we precompute, once per prime, a `Nat` bitmask `Q` whose bit `a` is set
exactly on the nonzero quadratic residues `a` mod `p`. Each character evaluation is then the bit
test `((Q >>> a) &&& 1).beq 1`. `qrMask` is the reference builder the certificate's supplied mask
is checked against; `qrLookupBool_spec` shows the bit test decides whether `a` is a nonzero
square mod `p`.
-/

/-- Reference quadratic-residue-mask builder: OR together `1 <<< (j² % p)` for `j = 1 .. fuel`. With
`fuel = (p-1)/2` this sets exactly the bits at the nonzero quadratic residues mod an odd prime `p`,
using `Nat` primitives only. -/
noncomputable def qrMaskGo : Nat → Nat → Nat :=
  Nat.rec (fun _ => 0)
    (fun k ih p => (ih p).lor (Nat.shiftLeft 1 (Nat.mod (Nat.mul (Nat.succ k) (Nat.succ k)) p)))

/-- The quadratic-residue bitmask mod `p`: bit `a` is set iff `a` is a nonzero square mod `p`. -/
noncomputable def qrMask (p : Nat) : Nat := qrMaskGo (Nat.div (Nat.sub p 1) 2) p

/-- The kernel bit test `(m >>> a) &&& 1 = 1` is `Nat.testBit m a`. -/
theorem shiftRight_land_one_eq_one_iff (m a : ℕ) :
    (m.shiftRight a).land 1 = 1 ↔ m.testBit a := by
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.land_eq, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq]
  constructor
  · intro h; simp [h]
  · intro h; simpa using of_decide_eq_true h

/-- Bit `a` of the fold is set iff some `1 ≤ j ≤ fuel` has `j² % p = a`. -/
theorem testBit_qrMaskGo (p : ℕ) (a : ℕ) :
    ∀ f : ℕ, Nat.testBit (qrMaskGo f p) a ↔ ∃ j, 1 ≤ j ∧ j ≤ f ∧ j * j % p = a := by
  intro f
  induction f with
  | zero =>
    simp only [qrMaskGo]
    constructor
    · rintro h; simp at h
    · rintro ⟨j, hj, hj0, _⟩; omega
  | succ k ih =>
    have hunfold : qrMaskGo (k + 1) p =
        (qrMaskGo k p).lor (Nat.shiftLeft 1 (Nat.mod (Nat.mul (Nat.succ k) (Nat.succ k)) p)) := rfl
    rw [hunfold, Nat.lor_eq, Nat.testBit_lor, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
      Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨j, hj1, hjk, hja⟩ | hb)
      · exact ⟨j, hj1, by omega, hja⟩
      · exact ⟨k + 1, by omega, by omega, of_decide_eq_true hb⟩
    · rintro ⟨j, hj1, hjk, hja⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hjk) with h | h
      · exact Or.inl ⟨j, hj1, by omega, hja⟩
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
  have hp3 : 3 ≤ p := by
    rcases hpp.two_le.lt_or_eq with h | h
    · omega
    · omega
  constructor
  · rintro ⟨j, hj1, hjk, hja⟩
    have hjp : j < p := by omega
    have hcast : (a : ZMod p) = (j : ZMod p) * (j : ZMod p) := by
      rw [← Nat.cast_mul, ← hja, ZMod.natCast_mod, Nat.cast_mul]
    refine ⟨?_, ⟨(j : ZMod p), hcast⟩⟩
    intro h0
    rw [h0] at hja
    have hdvd : p ∣ j * j := Nat.dvd_of_mod_eq_zero hja
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with hd | hd <;>
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
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
      omega
    by_cases hlow : v ≤ (p - 1) / 2
    · exact ⟨v, hv1, hlow, haeq⟩
    · refine ⟨p - v, by omega, by omega, ?_⟩
      have hsq : (p - v) * (p - v) % p = v * v % p := by
        have hkey : (((p - v) * (p - v) : ℕ) : ZMod p) = ((v * v : ℕ) : ZMod p) := by
          push_cast [Nat.cast_sub (by omega : v ≤ p)]
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

/-- Kernel-reducible character lookup: `true` iff bit `a` of the quadratic-residue mask `qmask` is
set, i.e. (for `qmask = qrMask p`, `a < p`, `p` odd prime) iff `a` is a nonzero square mod `p`. -/
noncomputable def qrLookupBool (qmask a : ℕ) : Bool := ((qmask.shiftRight a).land 1).beq 1

/-- The mask bit test decides whether `a` is a nonzero square mod `p` (for `a < p`, `p` an odd
prime). This is what lets a verified mask evaluate the descent character at each call site. -/
theorem qrLookupBool_spec (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    qrLookupBool (qrMask p) a = decide (a ≠ 0 ∧ IsSquare (a : ZMod p)) := by
  have hmask := qrMask_testBit p hp2 a ha
  rw [qrLookupBool]
  rcases eq_or_ne (((qrMask p).shiftRight a).land 1) 1 with h | h
  · rw [h, Nat.beq_refl]
    exact (decide_eq_true (hmask.mp h)).symm
  · have hbf : (((qrMask p).shiftRight a).land 1).beq 1 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact h
    rw [hbf]
    symm
    simp only [decide_eq_false_iff_not]
    exact fun hc => h (hmask.mpr hc)

/-! ### `psiCompute`: the kernel-reducible Legendre symbol into `ZMod 2` -/

/-- `Bool` mirror of `psiCompute`: `true` on non-residues (where `psiCompute = 1`), `false` on
residues (where `psiCompute = 0`). Evaluated via the quadratic-residue mask of `p`. -/
noncomputable def psiComputeBool (p : ℕ) (a : ZMod p) : Bool :=
  (qrLookupBool (qrMask p) a.val).not'

/-- Kernel-reducible replacement for `ECCompute.psi`. Reads the quadratic-residue mask of `p` at the
representative `a.val`: the symbol is `0` on quadratic residues and `1` on non-residues. -/
noncomputable def psiCompute (p : ℕ) (a : ZMod p) : ZMod 2 :=
  if psiComputeBool p a then 1 else 0

/-- For `p` an odd prime and `a ≠ 0`, `psiCompute` agrees with the abstract Legendre character
`psi`. -/
theorem psiCompute_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    psiCompute p a = psi p a := by
  have hp : p.Prime := Fact.out
  -- the natural-number value `a.val` casts back to `a`, and is `< p`
  have hval : ((a.val : ℤ) : ZMod p) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hval' : (a.val : ZMod p) = a := ZMod.natCast_zmod_val a
  have hvlt : a.val < p := ZMod.val_lt a
  have ha0 : a.val ≠ 0 := fun h => ha (by rw [← hval', h, Nat.cast_zero])
  -- the mask bit test decides `IsSquare a`
  have hspec := qrLookupBool_spec p hp2 a.val hvlt
  rw [hval'] at hspec
  rw [psiCompute, psiComputeBool, hspec]
  simp only [ne_eq, ha0, not_false_eq_true, true_and, Bool.not'_eq_not, psi]
  by_cases hsq : IsSquare a <;> simp [hsq]

/-! ### Kernel-reducible evaluation of `λ` on an affine point -/

/-- Kernel-reducible evaluation of the descent character `λ_{p,θ}` on an affine point with
`x`-coordinate `x`, using the mask-based `psiCompute` for the Legendre character. -/
noncomputable def lambdaCompute (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : ZMod 2 :=
  if (x.den : ZMod p) = 0 then 0
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psiCompute p (fderiv a₂ a₄ p θ)
       else psiCompute p ((x.num : ZMod p) - θ * (x.den : ZMod p))

/-- Under the descent hypotheses, `lambdaCompute` agrees with the abstract character `lambda` on
an affine point. -/
theorem lambdaCompute_eq (a₂ a₄ a₆ : ℤ) (p : ℕ) {θ : ZMod p}
    (hyp : DescentHyp a₂ a₄ a₆ p θ) (x y : ℚ)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    lambdaCompute a₂ a₄ p θ x = lambda a₂ a₄ a₆ p θ (.some x y h) := by
  have : Fact p.Prime := ⟨hyp.prime⟩
  have hp2 : p ≠ 2 := fun hp => hyp.ne_six (hp ▸ ⟨3, rfl⟩)
  have hfd : fderiv a₂ a₄ p θ ≠ 0 := fderiv_ne_zero hyp
  have hlam : lambda a₂ a₄ a₆ p θ (.some x y h) =
      if (x.den : ZMod p) = 0 then 0
      else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psi p (fderiv a₂ a₄ p θ)
           else psi p ((x.num : ZMod p) - θ * (x.den : ZMod p)) := rfl
  rw [lambdaCompute, hlam]
  grind [psiCompute_eq]

/-! ### `Bool`-valued mirror for kernel checks

`lambdaComputeBool` mirrors `lambdaCompute` in `Bool` (`1 ↦ true`, `0 ↦ false`), so certificate
matrix checks compare `Bool`s; `lambdaCompute_eq_bool` reads the result back into `ZMod 2`. -/

/-- `Bool` mirror of `lambdaCompute`, with `false`/`true` in place of `0`/`1 : ZMod 2`. -/
noncomputable def lambdaComputeBool (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : Bool :=
  if (x.den : ZMod p) = 0 then false
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psiComputeBool p (fderiv a₂ a₄ p θ)
       else psiComputeBool p ((x.num : ZMod p) - θ * (x.den : ZMod p))

/-- `lambdaCompute` is `lambdaComputeBool` read into `ZMod 2`. This lets a certificate check the
character matrix entirely over `Bool` and recover the `ZMod 2` value only at the end. -/
theorem lambdaCompute_eq_bool (a₂ a₄ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) :
    lambdaCompute a₂ a₄ p θ x = if lambdaComputeBool a₂ a₄ p θ x then 1 else 0 := by
  rw [lambdaCompute, lambdaComputeBool]
  grind [psiCompute]

/-! ### Fully `Nat` mirror: signed inputs as `mp - mn` pairs

`lambdaComputeBool` casts the signed `x.num`, `a₂`, `a₄` into `ZMod p`. `lambdaComputeBoolNatMask`
does the same computation in `Nat`: each signed value arrives as a difference `mp - mn` of two `ℕ`,
the modulus reduction is `(mp % p + (p - mn % p)) % p`, and the characters are bit tests against the
quadratic-residue mask `qmask` of `p`. It agrees with `lambdaComputeBool` through
`lambdaComputeBoolNatMask_eq` (given `qmask = qrMask p`, `p` an odd prime, and that the pairs
represent the inputs). -/

/-- Residue in `[0, p)` of `x.num - θ·x.den`, from the `mp - mn` pair `(xp, xm)` for `x.num` and the
label residue `tval` for `θ`. -/
noncomputable def alphaResNat (p tval xp xm xden : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.mod xp p) (Nat.sub p (Nat.mod (Nat.add xm (Nat.mul tval xden)) p))) p

/-- Residue in `[0, p)` of `f'(θ) = 3θ² + 2a₂θ + a₄`, from the `mp - mn` pairs `(c2p, c2m)` for `a₂`
and `(c4p, c4m)` for `a₄`. -/
noncomputable def fderivResNat (c2p c2m c4p c4m p tval : ℕ) : ℕ :=
  Nat.mod (Nat.add
    (Nat.mod
      (Nat.add (Nat.add (Nat.mul (Nat.mul 3 tval) tval) (Nat.mul (Nat.mul 2 c2p) tval)) c4p) p)
    (Nat.sub p (Nat.mod (Nat.add (Nat.mul (Nat.mul 2 c2m) tval) c4m) p))) p

/-- Fully `Nat` mirror of `lambdaComputeBool`; signed inputs carried as `mp - mn`, the two character
evaluations bit tests against a supplied quadratic-residue mask `qmask`. For `qmask = qrMask p`
(`p` an odd prime) it agrees with `lambdaComputeBool` (see `lambdaComputeBoolNatMask_eq`). -/
noncomputable def lambdaComputeBoolNatMask (c2p c2m c4p c4m p qmask tval xp xm xden : ℕ) : Bool :=
  ((Nat.mod xden p).beq 0).rec
    (((alphaResNat p tval xp xm xden).beq 0).rec
      ((qrLookupBool qmask (alphaResNat p tval xp xm xden)).not')
      ((qrLookupBool qmask (fderivResNat c2p c2m c4p c4m p tval)).not'))
    false

/-- `alphaResNat` casts back to `x.num - θ·x.den` in `ZMod p`. -/
private theorem alphaResNat_cast {p : ℕ} [NeZero p] (tval xp xm xden : ℕ) :
    ((alphaResNat p tval xp xm xden : ℕ) : ZMod p)
      = (xp : ZMod p) - ((xm : ZMod p) + (tval : ZMod p) * (xden : ZMod p)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hle : (xm + tval * xden) % p ≤ p := (Nat.mod_lt _ hp).le
  simp only [alphaResNat, Nat.mod_eq_mod, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub hle, ZMod.natCast_self, Nat.cast_mul]
  ring

/-- `fderivResNat` casts back to `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`. -/
private theorem fderivResNat_cast {p : ℕ} [NeZero p] (a₂ a₄ : ℤ) (θ : ZMod p)
    (c2p c2m c4p c4m tval : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) :
    ((fderivResNat c2p c2m c4p c4m p tval : ℕ) : ZMod p) = fderiv a₂ a₄ p θ := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hle : (2 * c2m * tval + c4m) % p ≤ p := (Nat.mod_lt _ hp).le
  simp only [fderivResNat, Nat.mod_eq_mod, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub hle, ZMod.natCast_self, Nat.cast_mul, Nat.cast_ofNat]
  subst hc2 hc4 htval
  unfold fderiv
  push_cast
  ring

/-- `alphaResNat` is the `ZMod p`-value of `x.num - θ·x.den`. -/
private theorem alphaResNat_eq_val {p : ℕ} [NeZero p] (θ : ZMod p) (x : ℚ) (tval xp xm xden : ℕ)
    (htval : (tval : ZMod p) = θ) (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    alphaResNat p tval xp xm xden = ((x.num : ZMod p) - θ * (x.den : ZMod p)).val := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hcast : ((alphaResNat p tval xp xm xden : ℕ) : ZMod p)
      = (x.num : ZMod p) - θ * (x.den : ZMod p) := by
    rw [alphaResNat_cast, ← htval, ← hxden]
    have : (x.num : ZMod p) = (xp : ZMod p) - (xm : ZMod p) := by rw [hxnum]; push_cast; ring
    rw [this]; ring
  have hlt : alphaResNat p tval xp xm xden < p := Nat.mod_lt _ hp
  rw [← hcast, ZMod.val_cast_of_lt hlt]

/-- `fderivResNat` is the `ZMod p`-value of `f'(θ)`. -/
private theorem fderivResNat_eq_val {p : ℕ} [NeZero p] (a₂ a₄ : ℤ) (θ : ZMod p)
    (c2p c2m c4p c4m tval : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) :
    fderivResNat c2p c2m c4p c4m p tval = (fderiv a₂ a₄ p θ).val := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hlt : fderivResNat c2p c2m c4p c4m p tval < p := Nat.mod_lt _ hp
  rw [← fderivResNat_cast a₂ a₄ θ c2p c2m c4p c4m tval hc2 hc4 htval,
    ZMod.val_cast_of_lt hlt]

/-- The mask-based `Nat` mirror agrees with `lambdaComputeBool` when `0 < p` and the pairs represent
the inputs (`a₂ = c2p - c2m`, `a₄ = c4p - c4m`, `θ = tval`, `x.num = xp - xm`, `xden = x.den`). The
mask is fixed to `qrMask p`, matching the character used by `psiComputeBool`. -/
theorem lambdaComputeBoolNatMask_eq (a₂ a₄ : ℤ) (p : ℕ) [NeZero p] (θ : ZMod p) (x : ℚ)
    (c2p c2m c4p c4m tval xp xm xden : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    lambdaComputeBoolNatMask c2p c2m c4p c4m p (qrMask p) tval xp xm xden
      = lambdaComputeBool a₂ a₄ p θ x := by
  have halpha := alphaResNat_eq_val θ x tval xp xm xden htval hxnum hxden
  have hfd := fderivResNat_eq_val a₂ a₄ θ c2p c2m c4p c4m tval hc2 hc4 htval
  have hden : (Nat.mod xden p = 0) = ((x.den : ZMod p) = 0) := by
    rw [hxden, Nat.mod_eq_mod, ← Nat.dvd_iff_mod_eq_zero, eq_iff_iff, ZMod.natCast_eq_zero_iff]
  rw [lambdaComputeBool, lambdaComputeBoolNatMask, psiComputeBool, psiComputeBool]
  simp only [Bool.rec_eq, Nat.beq_eq, Bool.not'_eq_not, halpha, hfd, hden, ZMod.val_eq_zero]

/-- Any integer is the difference of the `Nat`s `v.toNat` and `(-v).toNat` (one of them zero). This
is how a signed input is fed to `lambdaComputeBoolNatMask` as an `mp - mn` pair. -/
theorem int_toNat_sub (v : ℤ) : v = (v.toNat : ℤ) - ((-v).toNat : ℤ) := by omega

end ECCompute
