/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring
import ECCompute.Check.Fold

/-!
# Signed integers as pairs of `ℕ`, for kernel-reducible exact arithmetic

The exact checks (`checkPoints`, the exact 2-division cubic root) evaluate integer polynomials whose
coefficients and inputs are signed. Doing that in the kernel over `ℤ` unfolds `Int.casesOn` /
`Int.mul` / `Int.pow` per node. A pair `(p, n) : ℕ × ℕ` denotes `p - n : ℤ`, and `SN.add` / `SN.mul`
/ `SN.pow` / `SN.beq` run entirely in `Nat` (`Nat.add`, `Nat.mul`, `Nat.beq`), built with `Prod.rec`
and no equation compiler. Only the leaf injection `SN.ofInt` touches `Int` once per input value
(`Int.toNat`), the same unavoidable boundary as the descent character's `mp - mn` split.

`SN.value` reads a pair back to `ℤ`; the `value_*` lemmas show every operation matches its `ℤ`
counterpart, and `SN.beq_iff` reduces the `Bool` equality to `ℤ` equality, so a checker written over
pairs is proved correct against the ordinary `ℤ` statement.
-/

namespace ECCompute.SN

/-- The `ℤ` value `p - n` of a pair. -/
def value (a : ℕ × ℕ) : ℤ := (a.1 : ℤ) - (a.2 : ℤ)

/-- Inject `n : ℕ`. -/
def ofNat (n : ℕ) : ℕ × ℕ := (n, 0)

/-- Inject `v : ℤ` as `(v.toNat, (-v).toNat)` (one of the two is `0`). -/
noncomputable def ofInt (v : ℤ) : ℕ × ℕ := (v.toNat, (-v).toNat)

/-- Sum of two pairs, in `Nat`. -/
noncomputable def add (a b : ℕ × ℕ) : ℕ × ℕ :=
  a.rec fun ap an => b.rec fun bp bn => (Nat.add ap bp, Nat.add an bn)

/-- Negation: swap the two components. -/
noncomputable def neg (a : ℕ × ℕ) : ℕ × ℕ := a.rec fun ap an => (an, ap)

/-- Difference of two pairs. -/
noncomputable def sub (a b : ℕ × ℕ) : ℕ × ℕ := add a (neg b)

/-- Product of two pairs, in `Nat`: `(ap·bp + an·bn, ap·bn + an·bp)`. -/
noncomputable def mul (a b : ℕ × ℕ) : ℕ × ℕ :=
  a.rec fun ap an => b.rec fun bp bn =>
    (Nat.add (Nat.mul ap bp) (Nat.mul an bn), Nat.add (Nat.mul ap bn) (Nat.mul an bp))

/-- `a ^ k`, by `Nat.rec` on the exponent. -/
noncomputable def pow (a : ℕ × ℕ) : ℕ → ℕ × ℕ :=
  Nat.rec (ofNat 1) fun _ r => mul a r

/-- `Bool` equality of the two values, in `Nat`: `ap - an = bp - bn` iff `ap + bn = an + bp`. -/
noncomputable def beq (a b : ℕ × ℕ) : Bool :=
  a.rec fun ap an => b.rec fun bp bn => Nat.beq (Nat.add ap bn) (Nat.add an bp)

@[inherit_doc] scoped infixr:75 " ^ₛ " => ECCompute.SN.pow
@[inherit_doc] scoped infixl:70 " *ₛ " => ECCompute.SN.mul
@[inherit_doc] scoped infixl:65 " +ₛ " => ECCompute.SN.add
@[inherit_doc] scoped infixl:65 " -ₛ " => ECCompute.SN.sub

@[simp] theorem value_ofNat (n : ℕ) : value (ofNat n) = (n : ℤ) := by simp [value, ofNat]

@[simp] theorem value_ofInt (v : ℤ) : value (ofInt v) = v := by
  simp only [value, ofInt]; omega

@[simp] theorem value_add (a b : ℕ × ℕ) : value (add a b) = value a + value b := by
  obtain ⟨ap, an⟩ := a; obtain ⟨bp, bn⟩ := b
  simp only [value, add, Nat.add_eq, Nat.cast_add]; ring

@[simp] theorem value_neg (a : ℕ × ℕ) : value (neg a) = -value a := by
  obtain ⟨ap, an⟩ := a; simp only [value, neg]; ring

@[simp] theorem value_sub (a b : ℕ × ℕ) : value (sub a b) = value a - value b := by
  rw [sub, value_add, value_neg]; ring

@[simp] theorem value_mul (a b : ℕ × ℕ) : value (mul a b) = value a * value b := by
  obtain ⟨ap, an⟩ := a; obtain ⟨bp, bn⟩ := b
  simp only [value, mul, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul]; ring

theorem pow_succ_eq (a : ℕ × ℕ) (k : ℕ) : pow a (k + 1) = mul a (pow a k) := rfl

@[simp] theorem value_pow (a : ℕ × ℕ) (k : ℕ) : value (pow a k) = value a ^ k := by
  induction k with
  | zero => simp [pow, ofNat, value]
  | succ k ih => rw [pow_succ_eq, value_mul, ih, pow_succ]; ring

theorem beq_iff (a b : ℕ × ℕ) : beq a b = true ↔ value a = value b := by
  obtain ⟨ap, an⟩ := a; obtain ⟨bp, bn⟩ := b
  rw [beq, value, value]
  simp only [Nat.beq_eq, Nat.add_eq]
  omega

/-- `Bool` divisibility test `m ∣ value a`, in `Nat`: `ap - an ≡ 0 (mod m)` iff `ap % m = an % m`
(the modular checks like `f(θ) ≡ 0 (mod p)` use this). -/
noncomputable def dvd (a : ℕ × ℕ) (m : ℕ) : Bool :=
  a.rec fun ap an => Nat.beq (Nat.mod ap m) (Nat.mod an m)

theorem dvd_iff (a : ℕ × ℕ) (m : ℕ) : dvd a m = true ↔ (m : ℤ) ∣ value a := by
  obtain ⟨ap, an⟩ := a
  simp only [dvd, value, Nat.beq_eq]
  change Nat.ModEq m ap an ↔ (m : ℤ) ∣ ((ap : ℤ) - (an : ℤ))
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]

/-- `SN.dvd` matches the `Int.beq'` residue test, bridging the `Nat` checker to the `ℤ` form. -/
theorem dvd_eq_beq' (a : ℕ × ℕ) (m : ℕ) : dvd a m = Int.beq' (value a % (m : ℤ)) 0 := by
  have h1 : dvd a m = true ↔ value a % (m : ℤ) = 0 := by rw [dvd_iff, Int.dvd_iff_emod_eq_zero]
  have h2 : Int.beq' (value a % (m : ℤ)) 0 = true ↔ value a % (m : ℤ) = 0 := by rw [Int.beq'_eq]
  cases hd : dvd a m <;> cases hb : Int.beq' (value a % (m : ℤ)) 0 <;> simp_all

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p` (`0 < p`). Used by the modular
checkers to reduce a signed coefficient mod `p` before evaluating in `Nat`. -/
theorem intResNat_cast {p : ℕ} (hp : 0 < p) (z : ℤ) :
    (((z % (p : ℤ)).toNat : ℕ) : ZMod p) = (z : ZMod p) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact_mod_cast hp.ne')
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

end ECCompute.SN
