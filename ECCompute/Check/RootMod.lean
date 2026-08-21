/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import ECCompute.Soundness.Fold
import ECCompute.Check.IntResNat

/-!
# Ruling out roots of a monic integer polynomial by a residue search

For a monic integer polynomial given by a coefficient list `cs` and a modulus `ℓ`,
`monicHasRootMod` tries every residue `0, …, ℓ - 1` in `Nat` arithmetic. A `false` result rules out
an integer root, and for a monic quadratic a rational one.

## Main results

* `ECCompute.no_int_root_of_monicHasRootMod_eq_false`: a failed search rules out an integer root.
* `ECCompute.no_rat_root_of_monicHasRootMod_eq_false`: for a monic quadratic, it rules out a
  rational root.
-/

namespace ECCompute

/-! ## The monic residue search

One coefficient-list evaluator serves the cubic and the quadratic. A coefficient list `cs` runs
constant term first and ends with the leading `1`, so `[c₀, c₁, c₂, 1]` is `u³ + c₂u² + c₁u + c₀`
and `[c₀, c₁, 1]` is `u² + c₁u + c₀`. -/

/-- The monic integer polynomial with coefficient list `cs`, evaluated at `u`. -/
def monicEval (cs : List ℤ) (u : ℤ) : ℤ :=
  List.rec 0 (fun c _ acc => Int.add c (Int.mul u acc)) cs

/-- `monicEval` at `r` reduced mod `ℓ` in `Nat`, each coefficient taken to its residue as the fold
reaches it. -/
noncomputable def monicModL (cs : List ℤ) (ℓ r : ℕ) : ℕ :=
  List.rec 0 (fun c _ acc => Nat.mod (Nat.add (Int.emod c ℓ).toNat (Nat.mul r acc)) ℓ) cs

/-- A `monicModL` value is a residue mod `ℓ`. -/
theorem monicModL_lt {ℓ : ℕ} (hℓ : ℓ ≠ 0) (cs : List ℤ) (r : ℕ) : monicModL cs ℓ r < ℓ := by
  cases cs with
  | nil => exact Nat.pos_of_ne_zero hℓ
  | cons c t => exact Nat.mod_lt _ (Nat.pos_of_ne_zero hℓ)

/-- `monicModL` casts to `monicEval` in `ZMod ℓ`. -/
theorem monicModL_cast {ℓ : ℕ} [NeZero ℓ] (cs : List ℤ) (r : ℕ) :
    ((monicModL cs ℓ r : ℕ) : ZMod ℓ) = ((monicEval cs (r : ℤ) : ℤ) : ZMod ℓ) := by
  induction cs with
  | nil => simp [monicModL, monicEval]
  | cons c t ih =>
    have hstep : monicModL (c :: t) ℓ r
        = Nat.mod (Nat.add (Int.emod c ℓ).toNat (Nat.mul r (monicModL t ℓ r))) ℓ := rfl
    have hev : monicEval (c :: t) (r : ℤ) = c + (r : ℤ) * monicEval t (r : ℤ) := rfl
    rw [hstep, hev]
    simp only [Nat.mod_eq_mod, Nat.add_eq, Nat.mul_eq, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_mul, ← Int.mod_def', intResNat_cast, ih]
    push_cast
    ring

/-- The `Nat` residue test at `r` passes exactly when `monicEval cs r` vanishes in `ZMod ℓ`
(`ℓ ≠ 0`). -/
theorem monicModL_beq (cs : List ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (r : ℕ) :
    Nat.beq (monicModL cs ℓ r) 0 = true ↔ ((monicEval cs (r : ℤ) : ℤ) : ZMod ℓ) = 0 := by
  have : NeZero ℓ := ⟨hℓ⟩
  rw [Nat.beq_eq, ← natCast_eq_zero_iff_of_lt (monicModL_lt hℓ cs r), monicModL_cast cs r]

/-- Kernel-reducible test: `true` iff the monic integer polynomial with coefficients `cs` has a
root modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1` in `Nat` (mod `ℓ`). -/
noncomputable def monicHasRootMod (cs : List ℤ) (ℓ : ℕ) : Bool :=
  anyBelow ℓ fun r => Nat.beq (monicModL cs ℓ r) 0

/-- `monicEval` is invariant, modulo `n`, under changing its argument by a multiple of `n`. -/
theorem monicEval_modEq (cs : List ℤ) (n : ℤ) {a b : ℤ} (h : a ≡ b [ZMOD n]) :
    monicEval cs a ≡ monicEval cs b [ZMOD n] := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    have hev : ∀ u : ℤ, monicEval (c :: t) u = c + u * monicEval t u := fun _ => rfl
    rw [hev, hev]
    exact Int.ModEq.add_left c (h.mul ih)

/-- If the monic polynomial has no root mod `ℓ` (with `ℓ ≠ 0`), it has no integer root. -/
theorem no_int_root_of_monicHasRootMod_eq_false {cs : List ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : monicHasRootMod cs ℓ = false) (u : ℤ) : monicEval cs u ≠ 0 := by
  rw [monicHasRootMod, anyBelow_eq_false] at h
  have hres : ∀ r : ℕ, r < ℓ → ((monicEval cs (r : ℤ) : ℤ) : ZMod ℓ) ≠ 0 := fun r hr => by
    rw [ne_eq, ← monicModL_beq cs hℓ r, Bool.not_eq_true]; exact h r hr
  intro hu
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  set r : ℤ := u % (ℓ : ℤ) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg u (by exact_mod_cast hℓ)
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  have hrn : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  have hmodEq : (r.toNat : ℤ) ≡ u [ZMOD (ℓ : ℤ)] := by rw [hrn, hr]; exact Int.mod_modEq u _
  refine hres r.toNat (by omega) ?_
  have heq : ((monicEval cs (r.toNat : ℤ) : ℤ) : ZMod ℓ) = ((monicEval cs u : ℤ) : ZMod ℓ) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (monicEval_modEq cs (ℓ : ℤ) hmodEq)
  rw [heq, hu]
  simp

/-! ## Quadratic no-root lemmas (for the `t = 1` cofactor)

For the `t = 1` bound the `2`-division cubic factors as `(X - R) · q` with `q = X² + bX + c` an
irreducible quadratic; certifying that `q` has no rational root is done exactly as for the cubic,
by exhibiting a prime `ℓ` modulo which `q` has no root. -/

open Polynomial in
/-- If the monic integer quadratic `u² + b u + c` has no integer root, then it has no *rational*
root: by the rational root theorem, a rational root of a monic integer polynomial is an integer. -/
theorem no_rat_root_of_monicHasRootMod_eq_false {b c : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : monicHasRootMod [c, b, 1] ℓ = false) (x : ℚ)
    (hx : x ^ 2 + (b : ℚ) * x + (c : ℚ) = 0) : False := by
  set p : ℤ[X] := X ^ 2 + (C b * X + C c) with hp
  have hdeg : (C b * X + C c).degree < 2 := by
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    rw [max_lt_iff]
    exact ⟨lt_of_le_of_lt (degree_C_mul_X_le b) (by decide),
      lt_of_le_of_lt degree_C_le (by decide)⟩
  have hmonic : p.Monic := monic_X_pow_add hdeg
  have haeval : aeval x p = x ^ 2 + (b : ℚ) * x + (c : ℚ) := by
    simp only [hp, map_add, map_mul, map_pow, aeval_X, map_intCast, eq_intCast]
    ring
  have hroot : aeval x p = 0 := by rw [haeval, hx]
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  have hzcast : x = (z : ℚ) := by simp [hz]
  refine no_int_root_of_monicHasRootMod_eq_false hℓ h z ?_
  have hQ : ((monicEval [c, b, 1] z : ℤ) : ℚ) = 0 := by
    simp only [monicEval, Int.add_def, Int.mul_def]
    push_cast
    grind
  exact_mod_cast hQ

end ECCompute
