/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Defs
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A kernel-reducible descent character

The descent character `λ_{p,θ}` (`ECCompute.Descent.Defs`) is `noncomputable`, as `ECCompute.psi`
decides `IsSquare` classically. To evaluate `λ` inside a certificate we need a `rfl`-reducible
replacement. The heart is `jOdd`, a fuel-recursive evaluator for the Jacobi symbol `J(a | b)`
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

open scoped Classical

/-! ### The fuel-recursive Jacobi evaluator -/

/-- Fuel-recursive evaluator for the Jacobi symbol `J(a | b)`, valid when `b` is odd. One
reciprocity step per fuel unit:
* `b = 1`: `1`.  `a = 0` (with `b > 1`): `0`.  `a = 1`: `1`.
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

/-- The top-level kernel-reducible Jacobi symbol.  Reduce `a` modulo `p`, then run `jOdd` with
fuel `p` (which exceeds the reduced value `a % p < p`). -/
def jacobiFast (a : ℤ) (p : ℕ) : Int :=
  jOdd p (a % (p : ℤ)).toNat p

/-! ### Correctness: `jOdd` computes the Jacobi symbol -/

/-- For odd `b` and enough fuel, `jOdd` computes the Jacobi symbol. -/
theorem jOdd_eq : ∀ (fuel a b : ℕ), b % 2 = 1 → a < fuel →
    jOdd fuel a b = jacobiSym (a : ℤ) b := by
  intro fuel
  induction fuel with
  | zero => intro a b _ ha; exact absurd ha (Nat.not_lt_zero a)
  | succ fuel ih =>
    intro a b hb ha
    rw [jOdd]
    -- `b = 1`
    by_cases hb1 : b = 1
    · rw [if_pos hb1, hb1, jacobiSym.one_right]
    rw [if_neg hb1]
    -- `a = 0`
    by_cases ha0 : a = 0
    · rw [if_pos ha0, ha0, Nat.cast_zero, jacobiSym.zero_left (by omega)]
    rw [if_neg ha0]
    -- `a = 1`
    by_cases ha1 : a = 1
    · rw [if_pos ha1, ha1, Nat.cast_one, jacobiSym.one_left]
    rw [if_neg ha1]
    -- `a` even vs odd
    by_cases hae : a % 2 = 0
    · -- even: strip one factor of two
      rw [if_pos hae]
      have hlt : a / 2 < fuel := by omega
      have hIH := ih (a / 2) b hb hlt
      have hcast : ((a / 2 : ℕ) : ℤ) = (a : ℤ) / 2 := by
        rw [Int.natCast_ediv]; norm_num
      have hae' : (a : ℤ) % 2 = 0 := by
        have : ((a % 2 : ℕ) : ℤ) = ((a : ℤ)) % 2 := by rw [Int.natCast_emod]; norm_num
        rw [hae] at this; simpa using this.symm
      have he := jacobiSym.even_odd (a := (a : ℤ)) (b := b) hae' hb
      rw [hIH, hcast, ← he]
      split_ifs <;> ring
    · -- odd: quadratic reciprocity
      rw [if_neg hae]
      have ha2 : a % 2 = 1 := by omega
      have hapos : 0 < a := by omega
      have hmod_lt : b % a < a := Nat.mod_lt _ hapos
      have hlt : b % a < fuel := by omega
      have hIH := ih (b % a) a ha2 hlt
      have hcast : ((b % a : ℕ) : ℤ) = (b : ℤ) % a := by rw [Int.natCast_emod]
      have hml : jacobiSym ((b % a : ℕ) : ℤ) a = jacobiSym (b : ℤ) a := by
        rw [hcast, ← jacobiSym.mod_left]
      have hqr := jacobiSym.quadratic_reciprocity_if (a := a) (b := b) ha2 hb
      rw [hIH, hml, ← hqr]
      split_ifs <;> ring

/-- For `p` odd and positive, `jacobiFast a p = J(a | p)`. -/
theorem jacobiFast_eq (a : ℤ) (p : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    jacobiFast a p = jacobiSym a p := by
  have hred : ((a % (p : ℤ)).toNat : ℤ) = a % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))
  have hlt : (a % (p : ℤ)).toNat < p := by
    have h1 : a % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    omega
  rw [jacobiFast, jOdd_eq p _ p hodd hlt, hred, ← jacobiSym.mod_left]

/-! ### `psiCompute`: the kernel-reducible Legendre symbol into `ZMod 2` -/

/-- Kernel-reducible replacement for `ECCompute.psi`.  Uses `jacobiFast` on a representative of
`a`: the symbol is `0` on quadratic residues (`J = 1`) and `1` on non-residues (`J = -1`). -/
def psiCompute (p : ℕ) (a : ZMod p) : ZMod 2 :=
  if jacobiFast (a.val : ℤ) p = 1 then 0 else 1

/-- For `p` an odd prime and `a ≠ 0`, `psiCompute` agrees with the abstract Legendre character
`psi`. -/
theorem psiCompute_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    psiCompute p a = psi p a := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hpos : 0 < p := hp.pos
  -- the natural-number value `a.val` casts back to `a`, and is nonzero mod `p`
  have hval : ((a.val : ℤ) : ZMod p) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hval0 : ((a.val : ℤ) : ZMod p) ≠ 0 := by rw [hval]; exact ha
  -- `jacobiFast = jacobiSym = legendreSym`
  have hjf : jacobiFast (a.val : ℤ) p = legendreSym p (a.val : ℤ) := by
    rw [jacobiFast_eq _ _ hpos hodd, jacobiSym.legendreSym.to_jacobiSym]
  rw [psiCompute, psi, hjf]
  by_cases hsq : IsSquare a
  · rw [if_pos hsq, if_pos]
    rw [legendreSym.eq_one_iff p hval0, hval]; exact hsq
  · rw [if_neg hsq, if_neg]
    rw [legendreSym.eq_one_iff p hval0, hval]; exact hsq

/-! ### The derivative does not vanish at a simple root

Under `DescentHyp` the root `θ` is simple: `p ∤ Δ` forces `f'(θ) ≠ 0`, via the Bézout identity
`9·disc(f) = -A(θ)·f(θ) - B(θ)·f'(θ)` with `Δ = 16·disc(f)` and `p ∤ 6`. -/

/-- Under the descent hypotheses, the root `θ` is simple, so `f'(θ) ≠ 0`. -/
theorem fderiv_ne_zero (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime] {θ : ZMod p}
    (h : DescentHyp a₂ a₄ a₆ p θ) : fderiv a₂ a₄ a₆ p θ ≠ 0 := by
  intro hfd
  have hp3 : p ≠ 3 := fun hp => h.ne_six (hp ▸ ⟨2, rfl⟩)
  -- polynomial forms of `f(θ) = 0` and `f'(θ) = 0`
  have hf : θ ^ 3 + (a₂ : ZMod p) * θ ^ 2 + (a₄ : ZMod p) * θ + (a₆ : ZMod p) = 0 := h.root
  have hd : 3 * θ ^ 2 + 2 * (a₂ : ZMod p) * θ + (a₄ : ZMod p) = 0 := hfd
  -- Bézout: `9 · disc(f)` is a combination of `f(θ)` and `f'(θ)`, hence `0`.  With
  -- `s = 6a₄ - 2a₂²`, `t = 9a₆ - a₂a₄` and `L = 3sθ + 2a₂s - 3t` the cofactors are `9L` and
  -- `-(s² + L(3θ + a₂))`.
  have h9D : (9 : ZMod p) * (18 * (a₂ : ZMod p) * (a₄ : ZMod p) * (a₆ : ZMod p)
      - 4 * (a₂ : ZMod p) ^ 3 * (a₆ : ZMod p) + (a₂ : ZMod p) ^ 2 * (a₄ : ZMod p) ^ 2
      - 4 * (a₄ : ZMod p) ^ 3 - 27 * (a₆ : ZMod p) ^ 2) = 0 := by
    linear_combination
      (9 * (3 * (6 * (a₄ : ZMod p) - 2 * (a₂ : ZMod p) ^ 2) * θ
          + 2 * (a₂ : ZMod p) * (6 * (a₄ : ZMod p) - 2 * (a₂ : ZMod p) ^ 2)
          - 3 * (9 * (a₆ : ZMod p) - (a₂ : ZMod p) * (a₄ : ZMod p)))) * hf
      + (-((6 * (a₄ : ZMod p) - 2 * (a₂ : ZMod p) ^ 2) ^ 2
          + (3 * (6 * (a₄ : ZMod p) - 2 * (a₂ : ZMod p) ^ 2) * θ
            + 2 * (a₂ : ZMod p) * (6 * (a₄ : ZMod p) - 2 * (a₂ : ZMod p) ^ 2)
            - 3 * (9 * (a₆ : ZMod p) - (a₂ : ZMod p) * (a₄ : ZMod p)))
            * (3 * θ + (a₂ : ZMod p)))) * hd
  -- `9 ≠ 0` mod `p` (as `p ≠ 3`), so `disc(f) = 0`
  have : NeZero p := ⟨h.prime.pos.ne'⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    have hnd : ¬ p ∣ 3 :=
      fun hdvd => hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hdvd)
    simpa using (ZMod.natCast_eq_zero_iff 3 p).not.mpr hnd
  have h9 : (9 : ZMod p) ≠ 0 := by
    have : (9 : ZMod p) = 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h3 h3
  have hDzero := (mul_eq_zero.mp h9D).resolve_left h9
  -- but `Δ.num = 16 · disc(f)`, which is a unit mod `p`, contradiction
  have hΔ : (curve a₂ a₄ a₆).Δ.num =
      16 * (18 * a₂ * a₄ * a₆ - 4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3 - 27 * a₆ ^ 2) := by
    have : (curve a₂ a₄ a₆).Δ =
        ((16 * (18 * a₂ * a₄ * a₆ - 4 * a₂ ^ 3 * a₆ + a₂ ^ 2 * a₄ ^ 2 - 4 * a₄ ^ 3
          - 27 * a₆ ^ 2) : ℤ) : ℚ) := by
      simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      push_cast; ring
    rw [this, Rat.num_intCast]
  apply h.discr
  rw [hΔ]
  push_cast
  linear_combination (16 : ZMod p) * hDzero

/-! ### Kernel-reducible evaluation of `λ` on an affine point -/

/-- Kernel-reducible evaluation of the descent character `λ_{p,θ}` on an affine point with
`x`-coordinate `x`.  This is `ECCompute.lambda` with `psi` replaced by the computable
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
  have hfd : fderiv a₂ a₄ a₆ p θ ≠ 0 := fderiv_ne_zero a₂ a₄ a₆ p hyp
  have hlam : lambda a₂ a₄ a₆ p θ (.some x y h) =
      if (x.den : ZMod p) = 0 then 0
      else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psi p (fderiv a₂ a₄ a₆ p θ)
           else psi p ((x.num : ZMod p) - θ * (x.den : ZMod p)) := rfl
  rw [lambdaCompute, hlam]
  by_cases hd : (x.den : ZMod p) = 0
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]
    by_cases hα : (x.num : ZMod p) - θ * (x.den : ZMod p) = 0
    · rw [if_pos hα, if_pos hα, psiCompute_eq p hp2 hfd]
    · rw [if_neg hα, if_neg hα, psiCompute_eq p hp2 hα]

/-! ### `Bool`-valued mirror for fast kernel checks

`lambdaComputeBool` is `lambdaCompute` with its `ZMod 2` values replaced by `Bool` (`1 ↦ true`,
`0 ↦ false`), so certificate matrix checks compare `Bool`s; `lambdaCompute_eq_bool` reads the
result back into `ZMod 2`. -/

/-- `Bool` mirror of `psiCompute`: `true` on non-residues (where `psiCompute = 1`), `false` on
residues (where `psiCompute = 0`). -/
def psiComputeBool (p : ℕ) (a : ZMod p) : Bool :=
  if jacobiFast (a.val : ℤ) p = 1 then false else true

/-- `Bool` mirror of `lambdaCompute`, with `false`/`true` in place of `0`/`1 : ZMod 2`. -/
def lambdaComputeBool (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) : Bool :=
  if (x.den : ZMod p) = 0 then false
  else if (x.num : ZMod p) - θ * (x.den : ZMod p) = 0 then psiComputeBool p (fderiv a₂ a₄ a₆ p θ)
       else psiComputeBool p ((x.num : ZMod p) - θ * (x.den : ZMod p))

/-- `psiCompute` is `psiComputeBool` read into `ZMod 2` (`true ↦ 1`, `false ↦ 0`). -/
theorem psiCompute_eq_bool (p : ℕ) (a : ZMod p) :
    psiCompute p a = if psiComputeBool p a then 1 else 0 := by
  rw [psiCompute, psiComputeBool]; split <;> rfl

/-- `lambdaCompute` is `lambdaComputeBool` read into `ZMod 2`.  This lets a certificate check the
character matrix entirely over `Bool` and recover the `ZMod 2` value only at the end. -/
theorem lambdaCompute_eq_bool (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) (x : ℚ) :
    lambdaCompute a₂ a₄ a₆ p θ x = if lambdaComputeBool a₂ a₄ a₆ p θ x then 1 else 0 := by
  rw [lambdaCompute, lambdaComputeBool]
  by_cases hd : (x.den : ZMod p) = 0
  · rw [if_pos hd, if_pos hd]; rfl
  · rw [if_neg hd, if_neg hd]
    by_cases hα : (x.num : ZMod p) - θ * (x.den : ZMod p) = 0
    · rw [if_pos hα, if_pos hα, psiCompute_eq_bool]
    · rw [if_neg hα, if_neg hα, psiCompute_eq_bool]

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
