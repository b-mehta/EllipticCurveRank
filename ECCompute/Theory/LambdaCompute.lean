/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.PsiBase
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Bitwise

/-!
# A kernel-reducible descent character

The descent character `λ_{p,θ}` (`ECCompute.Descent.Defs`) is `noncomputable`, as `ECCompute.psi`
decides `IsSquare` classically. To evaluate `λ` inside a certificate we need a `rfl`-reducible
replacement. This is built on `jOdd`, a fuel-recursive evaluator for the Jacobi symbol `J(a | b)`
(`b` odd) by the gcd-style reciprocity algorithm; the fuel recursion reduces in the kernel.

## Main declarations

* `ECCompute.jOdd`: fuel-recursive Jacobi evaluator for odd `b`.
* `ECCompute.jacobiFast`: the top-level kernel-reducible Jacobi symbol `ℤ → ℕ → ℤ`.
* `ECCompute.jOdd_eq`: `jOdd fuel a b = jacobiSym a b` (enough fuel, `b` odd).
* `ECCompute.jacobiFast_eq`: `jacobiFast a p = jacobiSym a p` (`p` odd positive).
* `ECCompute.psiCompute`: kernel-reducible replacement for `psi`.
* `ECCompute.psiCompute_eq`: `psiCompute p a = psi p a` (`p` odd prime, `a ≠ 0`).
* `ECCompute.lambdaCompute`: kernel-reducible evaluation of `λ` on an affine point.
* `ECCompute.lambdaCompute_eq`: it agrees with the abstract `lambda`.
-/

namespace ECCompute

/-! ### The fuel-recursive Jacobi evaluator -/

/-- Fuel-recursive evaluator for the Jacobi symbol `J(a | b)`, valid when `b` is odd. One
reciprocity step per fuel unit:
* `b = 1`: `1`. `a = 0` (with `b > 1`): `0`. `a = 1`: `1`.
* `a` even: `J(a | b) = ±J(a/2 | b)`, sign `-1` when `b % 8 ∈ {3, 5}`.
* `a` odd (`a ≥ 3`): reciprocity `J(a | b) = ±J(b % a | a)`, sign `-1` when `a ≡ b ≡ 3 (mod 4)`.

The first argument strictly decreases, so any `fuel > a` suffices (`jacobiFast` uses `fuel = p`). -/
def jOdd : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if b = 1 then 1
    else if a = 0 then 0
    else if a = 1 then 1
    else if a % 2 = 0 then
      (if b % 8 = 3 ∨ b % 8 = 5 then -1 else 1) * jOdd fuel (a / 2) b
    else
      (if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1) * jOdd fuel (b % a) a

/-- The top-level kernel-reducible Jacobi symbol. Reduce `a` modulo `p`, then run `jOdd` with
fuel `p` (which exceeds the reduced value `a % p < p`). -/
def jacobiFast (a : ℤ) (p : ℕ) : Int :=
  jOdd p (a % (p : ℤ)).toNat p

/-! ### Correctness: `jOdd` computes the Jacobi symbol -/

/-- For odd `b` and enough fuel, `jOdd` computes the Jacobi symbol. -/
theorem jOdd_eq : ∀ (fuel a b : ℕ), b % 2 = 1 → a < fuel →
    jOdd fuel a b = jacobiSym (a : ℤ) b := by
  intro fuel
  induction fuel with
  | zero => lia
  | succ fuel ih =>
    intro a b hb ha
    rw [jOdd]
    -- `b = 1`
    obtain rfl | hb1 := eq_or_ne b 1
    · rw [if_pos rfl, jacobiSym.one_right]
    rw [if_neg hb1]
    -- `a = 0`
    obtain rfl | ha0 := eq_or_ne a 0
    · rw [if_pos rfl, Nat.cast_zero, jacobiSym.zero_left (by lia)]
    rw [if_neg ha0]
    -- `a = 1`
    obtain rfl | ha1 := eq_or_ne a 1
    · rw [if_pos rfl, Nat.cast_one, jacobiSym.one_left]
    rw [if_neg ha1]
    -- `a` even vs odd
    by_cases hae : a % 2 = 0
    · -- even: strip one factor of two
      rw [if_pos hae]
      have hIH := ih (a / 2) b hb (by lia)
      have hcast : ((a / 2 : ℕ) : ℤ) = (a : ℤ) / 2 := by rw [Int.natCast_ediv]; norm_num
      have hae' : (a : ℤ) % 2 = 0 := by lia
      rw [hIH, hcast, ← jacobiSym.even_odd (a := (a : ℤ)) (b := b) hae' hb]
      grind
    · -- odd: quadratic reciprocity
      rw [if_neg hae]
      have ha2 : a % 2 = 1 := by lia
      have hmod_lt : b % a < a := Nat.mod_lt _ (by lia)
      have hIH := ih (b % a) a ha2 (by lia)
      have hml : jacobiSym ((b % a : ℕ) : ℤ) a = jacobiSym (b : ℤ) a := by
        rw [Int.natCast_emod, ← jacobiSym.mod_left]
      rw [hIH, hml, ← jacobiSym.quadratic_reciprocity_if (a := a) (b := b) ha2 hb]
      grind

/-- For `p` odd and positive, `jacobiFast a p = J(a | p)`. -/
theorem jacobiFast_eq (a : ℤ) (p : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    jacobiFast a p = jacobiSym a p := by
  have hred : ((a % (p : ℤ)).toNat : ℤ) = a % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))
  have hlt : (a % (p : ℤ)).toNat < p := by
    have := Int.emod_lt_of_pos a (b := (p : ℤ)) (by exact_mod_cast hp); lia
  rw [jacobiFast, jOdd_eq p _ p hodd hlt, hred, ← jacobiSym.mod_left]

/-! ### `Nat`/`Bool` mirror of the Jacobi evaluator for kernel reduction

`jOdd` returns an `Int` to carry the reciprocity sign, so reducing it in the kernel unfolds
`Int.casesOn`/`Int.mul`. `jOddNat` is the `Bool` mirror: it threads the running sign in a `Bool`
`neg` (flipped by `Bool.rec neg neg.not'` at each step) and reports whether the signed symbol is
`1`. Built from `Nat.rec`/`Bool.rec`, `Nat.beq`, `Nat.mod`, `Nat.div` with no equation compiler and
no `Int`, so the kernel stays in `Nat`. It agrees with `jOdd` through `jOddNat_eq`. -/

/-- `Bool` mirror of `jOdd`: `true` iff `(-1)^neg · J(a | b) = 1`. See the section note. -/
noncomputable def jOddNat : Nat → Nat → Nat → Bool → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool → Bool) (fun _ _ _ => false)
    fun _ ih a b neg =>
      (b.beq 1).rec
        ((a.beq 0).rec
          ((a.beq 1).rec
            (((a.mod 2).beq 0).rec
              (ih (b.mod a) a ((((a.mod 4).beq 3).and' ((b.mod 4).beq 3)).rec neg neg.not'))
              (ih (a.div 2) b ((((b.mod 8).beq 3).or' ((b.mod 8).beq 5)).rec neg neg.not')))
            neg.not')
          false)
        neg.not'

theorem jOddNat_zero (a b : Nat) (neg : Bool) : jOddNat 0 a b neg = false := rfl

theorem jOddNat_succ (fuel a b : Nat) (neg : Bool) :
    jOddNat (fuel + 1) a b neg =
      (b.beq 1).rec
        ((a.beq 0).rec
          ((a.beq 1).rec
            (((a.mod 2).beq 0).rec
              (jOddNat fuel (b.mod a) a
                ((((a.mod 4).beq 3).and' ((b.mod 4).beq 3)).rec neg neg.not'))
              (jOddNat fuel (a.div 2) b
                ((((b.mod 8).beq 3).or' ((b.mod 8).beq 5)).rec neg neg.not')))
            neg.not')
          false)
        neg.not' := rfl

/-- The signed unit `(-1)^neg : ℤ`. -/
private def sgn (neg : Bool) : ℤ := if neg then -1 else 1

private theorem sgn_flip (neg : Bool) (P : Prop) [Decidable P] :
    sgn (if P then !neg else neg) = sgn neg * (if P then -1 else 1) := by
  by_cases P <;> cases neg <;> simp_all [sgn]

/-- `jOddNat` reports whether the signed Jacobi symbol `(-1)^neg · J(a | b)` equals `1`. -/
theorem jOddNat_eq (fuel a b : Nat) (neg : Bool) :
    jOddNat fuel a b neg = decide (sgn neg * jOdd fuel a b = 1) := by
  induction fuel generalizing a b neg with
  | zero => cases neg <;> simp [jOddNat_zero, jOdd, sgn]
  | succ f ih =>
    rw [jOddNat_succ, jOdd]
    have m2 : a.mod 2 = a % 2 := rfl
    have d2 : a.div 2 = a / 2 := rfl
    have mba : b.mod a = b % a := rfl
    have m4a : a.mod 4 = a % 4 := rfl
    have m4b : b.mod 4 = b % 4 := rfl
    have m8 : b.mod 8 = b % 8 := rfl
    simp only [Bool.rec_eq, Bool.and'_eq_and, Bool.or'_eq_or, Bool.not'_eq_not,
      Nat.beq_eq, Bool.and_eq_true, Bool.or_eq_true, m2, d2, mba, m4a, m4b, m8]
    by_cases hb : b = 1
    · cases neg <;> simp [hb, sgn]
    by_cases ha0 : a = 0
    · cases neg <;> simp [hb, ha0, sgn]
    by_cases ha1 : a = 1
    · cases neg <;> simp [hb, ha1, sgn]
    by_cases hae : a % 2 = 0
    · simp only [hb, ha0, ha1, hae, reduceIte]
      rw [ih, sgn_flip, mul_assoc]
    · simp only [hb, ha0, ha1, hae, reduceIte]
      rw [ih, sgn_flip, mul_assoc]

/-- Kernel-reducible `Bool`: `true` iff `J(a | p) = 1` for `a : ℕ`, the `Nat`-only mirror of
`jacobiFast (a : ℤ) p = 1`. -/
noncomputable def jacobiFastOne (a p : Nat) : Bool := jOddNat p (a.mod p) p false

theorem jacobiFastOne_eq (a p : Nat) : jacobiFastOne a p = decide (jacobiFast (a : ℤ) p = 1) := by
  have hmod : ((a : ℤ) % (p : ℤ)).toNat = a % p := by
    rw [← Int.natCast_mod, Int.toNat_natCast]
  have hmn : a.mod p = a % p := rfl
  rw [jacobiFastOne, jOddNat_eq, jacobiFast, hmod, hmn, sgn]
  simp

/-! ### Quadratic-residue bitmask: `O(1)` kernel evaluation of the Legendre character

For a fixed odd prime `p`, `jacobiFastOne · p` runs the reciprocity recursion (`~log p` `Nat.rec`
steps) on every call. Since the descent uses a small set of primes each many times, we instead
precompute, once per prime, a `Nat` bitmask `Q` whose bit `a` is set exactly on the nonzero
quadratic residues `a` mod `p`. Each character evaluation is then the native bit test
`((Q >>> a) &&& 1).beq 1` with no recursion. `qrMask` is the reference builder the certificate's
supplied mask is checked against; `jacobiLookup_eq` shows the bit test agrees with `jacobiFastOne`.
-/

/-- Reference quadratic-residue-mask builder: OR together `1 <<< (j² % p)` for `j = 1 .. fuel`. With
`fuel = (p-1)/2` this sets exactly the bits at the nonzero quadratic residues mod an odd prime `p`.
Nat primitives only, so it reduces in the kernel. -/
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

/-- The mask bit test agrees with `jacobiFastOne` for `a < p`, `p` an odd prime: both report whether
`a` is a nonzero quadratic residue mod `p`. This is what lets a verified mask replace the
reciprocity evaluation at each descent-character call site. -/
theorem jacobiLookup_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    (((qrMask p).shiftRight a).land 1).beq 1 = jacobiFastOne a p := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp2
  have hmask := qrMask_testBit p hp2 a ha
  rw [jacobiFastOne_eq, jacobiFast_eq _ _ hpp.pos hodd, ← jacobiSym.legendreSym.to_jacobiSym]
  have hlhs : (((qrMask p).shiftRight a).land 1).beq 1
      = decide (a ≠ 0 ∧ IsSquare (a : ZMod p)) := by
    rcases eq_or_ne (((qrMask p).shiftRight a).land 1) 1 with h | h
    · rw [h, Nat.beq_refl]
      exact (decide_eq_true (hmask.mp h)).symm
    · have hbf : (((qrMask p).shiftRight a).land 1).beq 1 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact h
      rw [hbf]
      symm
      simp only [decide_eq_false_iff_not]
      exact fun hc => h (hmask.mpr hc)
  rw [hlhs]
  congr 1
  by_cases ha0 : a = 0
  · subst ha0
    simp only [ne_eq, not_true_eq_false, false_and, Nat.cast_zero, legendreSym.at_zero]
    decide
  · have hne : ((a : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => ha0 (Nat.eq_zero_of_dvd_of_lt hd ha)
    rw [legendreSym.eq_one_iff p hne, Int.cast_natCast]
    simp only [ne_eq, ha0, not_false_eq_true, true_and]

/-- Kernel-reducible character lookup: `true` iff bit `a` of the quadratic-residue mask `qmask` is
set, i.e. (for `qmask = qrMask p`, `a < p`, `p` odd prime) iff `J(a | p) = 1`. Two native ops. -/
noncomputable def jacobiLookupBool (qmask a : ℕ) : Bool := ((qmask.shiftRight a).land 1).beq 1

theorem jacobiLookupBool_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a < p) :
    jacobiLookupBool (qrMask p) a = jacobiFastOne a p :=
  jacobiLookup_eq p hp2 a ha

/-! ### `psiCompute`: the kernel-reducible Legendre symbol into `ZMod 2` -/

/-- Kernel-reducible replacement for `ECCompute.psi`. Uses `jacobiFast` on a representative of
`a`: the symbol is `0` on quadratic residues (`J = 1`) and `1` on non-residues (`J = -1`). -/
def psiCompute (p : ℕ) (a : ZMod p) : ZMod 2 :=
  if jacobiFast (a.val : ℤ) p = 1 then 0 else 1

/-- For `p` an odd prime and `a ≠ 0`, `psiCompute` agrees with the abstract Legendre character
`psi`. -/
theorem psiCompute_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    psiCompute p a = psi p a := by
  have hp : p.Prime := Fact.out
  -- the natural-number value `a.val` casts back to `a`, and is nonzero mod `p`
  have hval : ((a.val : ℤ) : ZMod p) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  -- `jacobiFast = jacobiSym = legendreSym`
  have hjf : jacobiFast (a.val : ℤ) p = legendreSym p (a.val : ℤ) := by
    rw [jacobiFast_eq _ _ hp.pos (hp.eq_two_or_odd.resolve_left hp2),
      jacobiSym.legendreSym.to_jacobiSym]
  have hiff : legendreSym p (a.val : ℤ) = 1 ↔ IsSquare a := by
    rw [legendreSym.eq_one_iff p (hval.symm ▸ ha), hval]
  rw [psiCompute, psi, hjf]
  grind

/-! ### Kernel-reducible evaluation of `λ` on an affine point -/

/-- Kernel-reducible evaluation of the descent character `λ_{p,θ}` on an affine point with
`x`-coordinate `x`. This is `ECCompute.lambda` with `psi` replaced by the computable
`psiCompute`; it reduces to a value by `rfl` on concrete data. -/
def lambdaCompute (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : ZMod 2 :=
  if (x.den : ZMod p) = 0 then 0
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psiCompute p (fderiv a₂ a₄ a₆ p θ)
       else psiCompute p ((x.num : ZMod p) - θ * (x.den : ZMod p))

/-- Under the descent hypotheses, `lambdaCompute` agrees with the abstract character `lambda` on
an affine point. -/
theorem lambdaCompute_eq (a₂ a₄ a₆ : ℤ) (p : ℕ) {θ : ZMod p}
    (hyp : DescentHyp a₂ a₄ a₆ p θ) (x y : ℚ)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) :
    lambdaCompute a₂ a₄ a₆ p θ x = lambda a₂ a₄ a₆ p θ (.some x y h) := by
  have : Fact p.Prime := ⟨hyp.prime⟩
  have hp2 : p ≠ 2 := fun hp => hyp.ne_six (hp ▸ ⟨3, rfl⟩)
  have hfd : fderiv a₂ a₄ a₆ p θ ≠ 0 := fderiv_ne_zero hyp
  have hlam : lambda a₂ a₄ a₆ p θ (.some x y h) =
      if (x.den : ZMod p) = 0 then 0
      else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psi p (fderiv a₂ a₄ a₆ p θ)
           else psi p ((x.num : ZMod p) - θ * (x.den : ZMod p)) := rfl
  rw [lambdaCompute, hlam]
  grind [psiCompute_eq]

/-! ### `Bool`-valued mirror for fast kernel checks

`lambdaComputeBool` is `lambdaCompute` with its `ZMod 2` values replaced by `Bool` (`1 ↦ true`,
`0 ↦ false`), so certificate matrix checks compare `Bool`s; `lambdaCompute_eq_bool` reads the
result back into `ZMod 2`. -/

/-- `Bool` mirror of `psiCompute`: `true` on non-residues (where `psiCompute = 1`), `false` on
residues (where `psiCompute = 0`). -/
noncomputable def psiComputeBool (p : ℕ) (a : ZMod p) : Bool :=
  (jacobiFastOne a.val p).not'

/-- `Bool` mirror of `lambdaCompute`, with `false`/`true` in place of `0`/`1 : ZMod 2`. -/
noncomputable def lambdaComputeBool (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : Bool :=
  if (x.den : ZMod p) = 0 then false
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psiComputeBool p (fderiv a₂ a₄ a₆ p θ)
       else psiComputeBool p ((x.num : ZMod p) - θ * (x.den : ZMod p))

/-- `psiCompute` is `psiComputeBool` read into `ZMod 2` (`true ↦ 1`, `false ↦ 0`). -/
theorem psiCompute_eq_bool (p : ℕ) (a : ZMod p) :
    psiCompute p a = if psiComputeBool p a then 1 else 0 := by
  rw [psiCompute, psiComputeBool, jacobiFastOne_eq, Bool.not'_eq_not]
  by_cases h : jacobiFast (a.val : ℤ) p = 1 <;> simp [h]

/-- `lambdaCompute` is `lambdaComputeBool` read into `ZMod 2`. This lets a certificate check the
character matrix entirely over `Bool` and recover the `ZMod 2` value only at the end. -/
theorem lambdaCompute_eq_bool (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) :
    lambdaCompute a₂ a₄ a₆ p θ x = if lambdaComputeBool a₂ a₄ a₆ p θ x then 1 else 0 := by
  rw [lambdaCompute, lambdaComputeBool]
  grind [psiCompute_eq_bool]

/-! ### Fully `Nat` mirror: signed inputs as `mp - mn` pairs

`lambdaComputeBool` casts the signed `x.num`, `a₂`, `a₄` into `ZMod p`, so the kernel unfolds
`Int.cast` and the whole `Fin`/`ZMod` layer. `lambdaComputeBoolNat` does the same computation in
`Nat`: each signed value arrives as a difference `mp - mn` of two `ℕ`, the modulus reduction is
`(mp % p + (p - mn % p)) % p`, and the characters compare through `jacobiFastOne`. Nothing but
`Nat.add`, `Nat.mul`, `Nat.mod`, `Nat.sub`, `Nat.beq` and `Bool.rec` reduces in the kernel. It
agrees with `lambdaComputeBool` through `lambdaComputeBoolNat_eq` (given `0 < p` and that the pairs
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

/-- Fully `Nat` mirror of `lambdaComputeBool`; signed inputs carried as `mp - mn`. -/
noncomputable def lambdaComputeBoolNat (c2p c2m c4p c4m p tval xp xm xden : ℕ) : Bool :=
  ((Nat.mod xden p).beq 0).rec
    (((alphaResNat p tval xp xm xden).beq 0).rec
      ((jacobiFastOne (alphaResNat p tval xp xm xden) p).not')
      ((jacobiFastOne (fderivResNat c2p c2m c4p c4m p tval) p).not'))
    false

/-- Mask variant of `lambdaComputeBoolNat`: the two `jacobiFastOne · p` reciprocity evaluations are
replaced by native bit tests against a supplied quadratic-residue mask `qmask`. For `qmask = qrMask
p` (`p` an odd prime) it agrees with `lambdaComputeBoolNat` (see `lambdaComputeBoolNatMask_eq`); the
mask is built and checked once per prime, so each of these evaluations is recursion-free. -/
noncomputable def lambdaComputeBoolNatMask (c2p c2m c4p c4m p qmask tval xp xm xden : ℕ) : Bool :=
  ((Nat.mod xden p).beq 0).rec
    (((alphaResNat p tval xp xm xden).beq 0).rec
      ((jacobiLookupBool qmask (alphaResNat p tval xp xm xden)).not')
      ((jacobiLookupBool qmask (fderivResNat c2p c2m c4p c4m p tval)).not'))
    false

/-- With the correct mask (`qmask = qrMask p`, `p` an odd prime) the mask variant computes the same
`Bool` as `lambdaComputeBoolNat`. -/
theorem lambdaComputeBoolNatMask_eq (p qmask : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hq : qmask = qrMask p) (c2p c2m c4p c4m tval xp xm xden : ℕ) :
    lambdaComputeBoolNatMask c2p c2m c4p c4m p qmask tval xp xm xden
      = lambdaComputeBoolNat c2p c2m c4p c4m p tval xp xm xden := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  subst hq
  have h1 : jacobiLookupBool (qrMask p) (alphaResNat p tval xp xm xden)
      = jacobiFastOne (alphaResNat p tval xp xm xden) p :=
    jacobiLookupBool_eq p hp2 _ (Nat.mod_lt _ hp)
  have h2 : jacobiLookupBool (qrMask p) (fderivResNat c2p c2m c4p c4m p tval)
      = jacobiFastOne (fderivResNat c2p c2m c4p c4m p tval) p :=
    jacobiLookupBool_eq p hp2 _ (Nat.mod_lt _ hp)
  unfold lambdaComputeBoolNatMask lambdaComputeBoolNat
  rw [h1, h2]

private theorem natPrim (x y : ℕ) :
    Nat.mod x y = x % y ∧ Nat.add x y = x + y ∧ Nat.sub x y = x - y ∧ Nat.mul x y = x * y :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `alphaResNat` casts back to `x.num - θ·x.den` in `ZMod p`. -/
private theorem alphaResNat_cast {p : ℕ} (hp : 0 < p) (tval xp xm xden : ℕ) :
    ((alphaResNat p tval xp xm xden : ℕ) : ZMod p)
      = (xp : ZMod p) - ((xm : ZMod p) + (tval : ZMod p) * (xden : ZMod p)) := by
  have hle : (xm + tval * xden) % p ≤ p := (Nat.mod_lt _ hp).le
  simp only [alphaResNat, (natPrim _ _).1, (natPrim _ _).2.1, (natPrim _ _).2.2.1,
    (natPrim _ _).2.2.2, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hle, ZMod.natCast_self,
    Nat.cast_mul]
  ring

/-- `fderivResNat` casts back to `f'(θ) = 3θ² + 2a₂θ + a₄` in `ZMod p`. -/
private theorem fderivResNat_cast {p : ℕ} (hp : 0 < p) (a₂ a₄ a₆ : ℤ) (θ : ZMod p)
    (c2p c2m c4p c4m tval : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) :
    ((fderivResNat c2p c2m c4p c4m p tval : ℕ) : ZMod p) = fderiv a₂ a₄ a₆ p θ := by
  have hle : (2 * c2m * tval + c4m) % p ≤ p := (Nat.mod_lt _ hp).le
  simp only [fderivResNat, (natPrim _ _).1, (natPrim _ _).2.1, (natPrim _ _).2.2.1,
    (natPrim _ _).2.2.2, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hle, ZMod.natCast_self,
    Nat.cast_mul, Nat.cast_ofNat]
  subst hc2 hc4 htval
  unfold fderiv
  push_cast
  ring

/-- `alphaResNat` is the `ZMod p`-value of `x.num - θ·x.den`. -/
private theorem alphaResNat_eq_val {p : ℕ} (hp : 0 < p) (θ : ZMod p) (x : ℚ) (tval xp xm xden : ℕ)
    (htval : (tval : ZMod p) = θ) (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    alphaResNat p tval xp xm xden = ((x.num : ZMod p) - θ * (x.den : ZMod p)).val := by
  have hcast : ((alphaResNat p tval xp xm xden : ℕ) : ZMod p)
      = (x.num : ZMod p) - θ * (x.den : ZMod p) := by
    rw [alphaResNat_cast hp, ← htval, ← hxden]
    have : (x.num : ZMod p) = (xp : ZMod p) - (xm : ZMod p) := by rw [hxnum]; push_cast; ring
    rw [this]; ring
  rw [← hcast, ZMod.val_cast_of_lt (show alphaResNat p tval xp xm xden < p from Nat.mod_lt _ hp)]

/-- `fderivResNat` is the `ZMod p`-value of `f'(θ)`. -/
private theorem fderivResNat_eq_val {p : ℕ} (hp : 0 < p) (a₂ a₄ a₆ : ℤ) (θ : ZMod p)
    (c2p c2m c4p c4m tval : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) :
    fderivResNat c2p c2m c4p c4m p tval = (fderiv a₂ a₄ a₆ p θ).val := by
  rw [← fderivResNat_cast hp a₂ a₄ a₆ θ c2p c2m c4p c4m tval hc2 hc4 htval,
    ZMod.val_cast_of_lt (show fderivResNat c2p c2m c4p c4m p tval < p from Nat.mod_lt _ hp)]

/-- The fully-`Nat` mirror agrees with `lambdaComputeBool` when `0 < p` and the pairs represent the
inputs (`a₂ = c2p - c2m`, `a₄ = c4p - c4m`, `θ = tval`, `x.num = xp - xm`, `xden = x.den`). -/
theorem lambdaComputeBoolNat_eq (a₂ a₄ a₆ : ℤ) (p : ℕ) (hp : 0 < p) (θ : ZMod p) (x : ℚ)
    (c2p c2m c4p c4m tval xp xm xden : ℕ) (hc2 : a₂ = (c2p : ℤ) - c2m) (hc4 : a₄ = (c4p : ℤ) - c4m)
    (htval : (tval : ZMod p) = θ) (hxnum : x.num = (xp : ℤ) - xm) (hxden : xden = x.den) :
    lambdaComputeBoolNat c2p c2m c4p c4m p tval xp xm xden = lambdaComputeBool a₂ a₄ a₆ p θ x := by
  have halpha := alphaResNat_eq_val hp θ x tval xp xm xden htval hxnum hxden
  have hfd := fderivResNat_eq_val hp a₂ a₄ a₆ θ c2p c2m c4p c4m tval hc2 hc4 htval
  have hden : (Nat.mod xden p = 0) = ((x.den : ZMod p) = 0) := by
    rw [hxden, (natPrim _ _).1, ← Nat.dvd_iff_mod_eq_zero, eq_iff_iff,
      ZMod.natCast_eq_zero_iff]
  rw [lambdaComputeBool, lambdaComputeBoolNat, psiComputeBool, psiComputeBool]
  simp only [Bool.rec_eq, Nat.beq_eq, Bool.not'_eq_not, halpha, hfd, hden, ZMod.val_eq_zero]

/-- Any integer is the difference of the `Nat`s `v.toNat` and `(-v).toNat` (one of them zero). This
is how a signed input is fed to `lambdaComputeBoolNat` as an `mp - mn` pair. -/
theorem int_toNat_sub (v : ℤ) : v = (v.toNat : ℤ) - ((-v).toNat : ℤ) := by omega

/-- The `Nat` residue `(z % p).toNat` casts back to `z` in `ZMod p` (`0 < p`); this is how a label
representative `θ : ℤ` becomes the `Nat` residue `tval` fed to `lambdaComputeBoolNat`. -/
theorem intModToNat_cast {p : ℕ} (hp : 0 < p) (z : ℤ) :
    (((z % (p : ℤ)).toNat : ℕ) : ZMod p) = (z : ZMod p) := by
  have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg z (by exact_mod_cast hp.ne')
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

/-! ### Worked examples: kernel reduction by `rfl`

Each of these closes by `rfl`, confirming the reciprocity evaluator reduces in the kernel. -/

/-- `3` is a non-residue mod `7`: `J(3 | 7) = -1`. -/
example : jacobiFast 3 7 = -1 := rfl

/-- `2` is a residue mod `7` (`3² ≡ 2`): `J(2 | 7) = 1`. -/
example : jacobiFast 2 7 = 1 := rfl

/-- A larger reciprocity/gcd descent still reduces instantly: `J(1001 | 9907) = -1`. -/
example : jacobiFast 1001 9907 = -1 := rfl

/-- `psiCompute` sends a non-residue to `1`. -/
example : psiCompute 7 (3 : ZMod 7) = 1 := rfl

/-- `psiCompute` sends a residue to `0`. -/
example : psiCompute 7 (2 : ZMod 7) = 0 := rfl

/-- `lambdaCompute` reduces to a value by `rfl`: for `y² = x³ - x`, label `(7, 0)`, and the
point with `x = 2`, we get `α = 2` (a residue), so `λ = 0`. -/
example : lambdaCompute 0 (-1) 0 7 (0 : ZMod 7) (2 : ℚ) = 0 := rfl

end ECCompute
