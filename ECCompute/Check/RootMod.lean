/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import ECCompute.Check.Fold
import ECCompute.Check.IntResNat

/-!
# Ruling out roots of a monic integer polynomial by a residue search

For a monic integer cubic `u³ + c₂u² + c₁u + c₀` or quadratic `u² + bu + c` and a modulus `ℓ`,
`cubicHasRootMod` and `quadHasRootMod` try every residue `0, …, ℓ - 1` in `Nat` arithmetic. A
`false` result rules out an integer root, and for the quadratic a rational one.

## Main definitions

* `ECCompute.cubicEval`, `ECCompute.quadEval`: the polynomial values over `ℤ`.
* `ECCompute.cubicEvalK`: `cubicEval` in the raw `Int` primitives the kernel reduces.
* `ECCompute.cubicHasRootMod`, `ECCompute.quadHasRootMod`: the residue searches.

## Main results

* `ECCompute.no_int_root_of_cubicHasRootMod_eq_false`: a failed cubic search rules out an integer
  root.
* `ECCompute.no_int_root_of_quadHasRootMod_eq_false`,
  `ECCompute.no_rat_root_of_quadHasRootMod_eq_false`: the same for the quadratic, over `ℤ` and
  over `ℚ`.

## Implementation notes

The cubic and quadratic halves share their shape: a `Nat` residue evaluation, a `_beq` lemma
matching it against the `ℤ` residue test, and a no-root consequence. They are written out
separately because both are reduced by the kernel for every certificate, and the straight-line
`Nat` form is the one the certificates are built against. Only `no_int_root_of_anyBelow` is shared.
-/

namespace ECCompute

/-! ## The cubic case -/

/-- The value of the monic cubic `u³ + c₂u² + c₁u + c₀` at an integer `u`. -/
def cubicEval (c₂ c₁ c₀ u : ℤ) : ℤ := u ^ 3 + c₂ * u ^ 2 + c₁ * u + c₀

/-- `cubicEval` written in the raw `Int.mul`/`Int.add` primitives, with the powers expanded, so the
kernel reduces it directly. Equals `cubicEval` by `cubicEvalK_eq`. -/
def cubicEvalK (c₂ c₁ c₀ u : ℤ) : ℤ :=
  Int.add (Int.add (Int.add (Int.mul (Int.mul u u) u) (Int.mul c₂ (Int.mul u u)))
    (Int.mul c₁ u)) c₀

/-- The kernel form `cubicEvalK` computes `cubicEval`. -/
theorem cubicEvalK_eq (c₂ c₁ c₀ u : ℤ) : cubicEvalK c₂ c₁ c₀ u = cubicEval c₂ c₁ c₀ u := by
  have hmul : ∀ a b : ℤ, Int.mul a b = a * b := fun _ _ => rfl
  have hadd : ∀ a b : ℤ, Int.add a b = a + b := fun _ _ => rfl
  simp only [cubicEvalK, cubicEval, hmul, hadd]
  ring

/-- The cubic evaluated at `r`, reduced mod `ℓ` in `Nat`, from coefficients already reduced to the
residues `d₂ d₁ d₀ ∈ [0, ℓ)`. -/
noncomputable def cubicModL (d₂ d₁ d₀ ℓ r : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mul r r) r) (Nat.mul d₂ (Nat.mul r r)))
    (Nat.mul d₁ r)) d₀) ℓ

/-- The mod-`ℓ` `Nat` cubic test matches the `ℤ` residue test. -/
theorem cubicModL_beq (c₂ c₁ c₀ : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (r : ℕ) :
    Nat.beq (cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r) 0
      = Int.beq' (cubicEval c₂ c₁ c₀ (r : ℤ) % (ℓ : ℤ)) 0 := by
  have : NeZero ℓ := ⟨hℓ⟩
  have hlt : cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r < ℓ :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hℓ)
  have em : ∀ x y : ℕ, Nat.mod x y = x % y := fun _ _ => rfl
  have ea : ∀ x y : ℕ, Nat.add x y = x + y := fun _ _ => rfl
  have el : ∀ x y : ℕ, Nat.mul x y = x * y := fun _ _ => rfl
  have hcast : ((cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r : ℕ) : ZMod ℓ)
      = (cubicEval c₂ c₁ c₀ (r : ℤ) : ZMod ℓ) := by
    simp only [cubicModL, cubicEval, em, ea, el, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_mul, intResNat_cast]
    push_cast; ring
  have hnz : ((cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r : ℕ) : ZMod ℓ) = 0
      ↔ cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r = 0 := by
    rw [← ZMod.val_eq_zero, ZMod.val_cast_of_lt hlt]
  have h1 : Nat.beq (cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r) 0 = true
      ↔ (ℓ : ℤ) ∣ cubicEval c₂ c₁ c₀ (r : ℤ) := by
    rw [Nat.beq_eq, ← hnz, hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : Int.beq' (cubicEval c₂ c₁ c₀ (r : ℤ) % (ℓ : ℤ)) 0 = true
      ↔ (ℓ : ℤ) ∣ cubicEval c₂ c₁ c₀ (r : ℤ) := by rw [Int.beq'_eq, Int.dvd_iff_emod_eq_zero]
  cases hn : Nat.beq (cubicModL (c₂ % ℓ).toNat (c₁ % ℓ).toNat (c₀ % ℓ).toNat ℓ r) 0 <;>
    cases hi : Int.beq' (cubicEval c₂ c₁ c₀ (r : ℤ) % (ℓ : ℤ)) 0 <;> simp_all

/-- Kernel-reducible test: `true` iff the monic integer cubic `u³ + c₂u² + c₁u + c₀` has a root
modulo `ℓ`, checked by trying every residue `0, …, ℓ - 1` in `Nat` (mod `ℓ`). -/
noncomputable def cubicHasRootMod (c₂ c₁ c₀ : ℤ) (ℓ : ℕ) : Bool :=
  anyBelow ℓ fun r =>
    Nat.beq (cubicModL (Int.emod c₂ ℓ).toNat (Int.emod c₁ ℓ).toNat (Int.emod c₀ ℓ).toNat ℓ r) 0

/-- The `Nat` cubic search agrees with the `ℤ` residue search over `0, …, ℓ - 1`. -/
theorem cubicHasRootMod_eq (c₂ c₁ c₀ : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    cubicHasRootMod c₂ c₁ c₀ ℓ
      = anyBelow ℓ fun r => Int.beq' (cubicEval c₂ c₁ c₀ (r : ℤ) % (ℓ : ℤ)) 0 := by
  rw [cubicHasRootMod]
  congr 1
  funext r
  rw [← Int.mod_def', ← Int.mod_def', ← Int.mod_def', cubicModL_beq c₂ c₁ c₀ hℓ r]

/-- `cubicEval` is invariant, modulo `ℓ`, under changing its argument by a multiple of `ℓ`. -/
theorem cubicEval_modEq {c₂ c₁ c₀ : ℤ} (ℓ : ℤ) {a a' : ℤ} (h : a ≡ a' [ZMOD ℓ]) :
    cubicEval c₂ c₁ c₀ a ≡ cubicEval c₂ c₁ c₀ a' [ZMOD ℓ] := by
  unfold cubicEval
  gcongr

/-- A `ℤ → ℤ` map invariant mod `ℓ` (`hmod`) that fails the `anyBelow ℓ` residue test (`h`) has no
integer root. -/
private theorem no_int_root_of_anyBelow {eval : ℤ → ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hmod : ∀ {a b : ℤ}, a ≡ b [ZMOD (ℓ : ℤ)] → eval a ≡ eval b [ZMOD (ℓ : ℤ)])
    (h : anyBelow ℓ (fun r => Int.beq' (eval (r : ℤ) % (ℓ : ℤ)) 0) = false) (u : ℤ) :
    eval u ≠ 0 := by
  intro hu
  -- reduce `u` to its residue `r = u % ℓ ∈ {0, …, ℓ-1}`
  set r : ℤ := u % (ℓ : ℤ) with hr
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  have hr0 : 0 ≤ r := Int.emod_nonneg u (by exact_mod_cast hℓ)
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  -- `r.toNat` is congruent to `u` mod `ℓ`, and `eval` at `u` is `0`, so the residue is a root
  have hcong : eval (r.toNat : ℤ) % (ℓ : ℤ) = 0 := by
    have huv : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    have hmodEq : (r.toNat : ℤ) ≡ u [ZMOD (ℓ : ℤ)] := by rw [huv, hr]; exact Int.mod_modEq u _
    have hthis : eval (r.toNat : ℤ) % (ℓ : ℤ) = eval u % (ℓ : ℤ) := hmod hmodEq
    rw [hthis, hu, Int.zero_emod]
  -- but the test is `false`, i.e. no tested residue is a root, a contradiction
  rw [anyBelow_eq_false] at h
  grind [Int.beq'_ne]

/-- If the monic cubic has no root mod `ℓ` (with `ℓ ≠ 0`), it has no integer root. -/
theorem no_int_root_of_cubicHasRootMod_eq_false {c₂ c₁ c₀ : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : cubicHasRootMod c₂ c₁ c₀ ℓ = false) (u : ℤ) : cubicEval c₂ c₁ c₀ u ≠ 0 := by
  rw [cubicHasRootMod_eq _ _ _ hℓ] at h
  exact no_int_root_of_anyBelow hℓ (cubicEval_modEq (ℓ : ℤ)) h u

/-! ## The quadratic case

For the `t = 1` bound the `2`-division cubic factors as `(X - R) · q` with `q = X² + bX + c` an
irreducible quadratic; certifying that `q` has no rational root exhibits a prime `ℓ` modulo which
`q` has no root. -/

/-- The value of the monic quadratic `u² + b u + c` at an integer `u`. -/
def quadEval (b c u : ℤ) : ℤ := u ^ 2 + b * u + c

/-- The quadratic evaluated at `r`, reduced mod `ℓ` in `Nat`, from residues `d₁ d₀ ∈ [0, ℓ)`. -/
noncomputable def quadModL (d₁ d₀ ℓ r : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.mul r r) (Nat.mul d₁ r)) d₀) ℓ

/-- The mod-`ℓ` `Nat` quadratic test matches the `ℤ` residue test. -/
theorem quadModL_beq (b c : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (r : ℕ) :
    Nat.beq (quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r) 0
      = Int.beq' (quadEval b c (r : ℤ) % (ℓ : ℤ)) 0 := by
  have : NeZero ℓ := ⟨hℓ⟩
  have hlt : quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r < ℓ :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hℓ)
  have em : ∀ x y : ℕ, Nat.mod x y = x % y := fun _ _ => rfl
  have ea : ∀ x y : ℕ, Nat.add x y = x + y := fun _ _ => rfl
  have el : ∀ x y : ℕ, Nat.mul x y = x * y := fun _ _ => rfl
  have hcast : ((quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r : ℕ) : ZMod ℓ)
      = (quadEval b c (r : ℤ) : ZMod ℓ) := by
    simp only [quadModL, quadEval, em, ea, el, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
      intResNat_cast]
    push_cast; ring
  have hnz : ((quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r : ℕ) : ZMod ℓ) = 0
      ↔ quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r = 0 := by
    rw [← ZMod.val_eq_zero, ZMod.val_cast_of_lt hlt]
  have h1 : Nat.beq (quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r) 0 = true
      ↔ (ℓ : ℤ) ∣ quadEval b c (r : ℤ) := by
    rw [Nat.beq_eq, ← hnz, hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : Int.beq' (quadEval b c (r : ℤ) % (ℓ : ℤ)) 0 = true
      ↔ (ℓ : ℤ) ∣ quadEval b c (r : ℤ) := by rw [Int.beq'_eq, Int.dvd_iff_emod_eq_zero]
  cases hn : Nat.beq (quadModL (b % ℓ).toNat (c % ℓ).toNat ℓ r) 0 <;>
    cases hi : Int.beq' (quadEval b c (r : ℤ) % (ℓ : ℤ)) 0 <;> simp_all

/-- Kernel-reducible test: `true` iff the monic integer quadratic `u² + b u + c` has a root modulo
`ℓ`, checked by trying every residue `0, …, ℓ - 1` in `Nat` (mod `ℓ`). -/
noncomputable def quadHasRootMod (b c : ℤ) (ℓ : ℕ) : Bool :=
  anyBelow ℓ fun r => Nat.beq (quadModL (Int.emod b ℓ).toNat (Int.emod c ℓ).toNat ℓ r) 0

/-- The `Nat` quadratic search agrees with the `ℤ` residue search over `0, …, ℓ - 1`. -/
theorem quadHasRootMod_eq (b c : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    quadHasRootMod b c ℓ = anyBelow ℓ fun r => Int.beq' (quadEval b c (r : ℤ) % (ℓ : ℤ)) 0 := by
  rw [quadHasRootMod]
  congr 1
  funext r
  rw [← Int.mod_def', ← Int.mod_def', quadModL_beq b c hℓ r]

/-- `quadEval` is invariant, modulo `ℓ`, under changing its argument by a multiple of `ℓ`. -/
theorem quadEval_modEq {b c : ℤ} (ℓ : ℤ) {a a' : ℤ} (h : a ≡ a' [ZMOD ℓ]) :
    quadEval b c a ≡ quadEval b c a' [ZMOD ℓ] := by
  unfold quadEval
  gcongr

/-- If the monic quadratic has no root mod `ℓ` (with `ℓ ≠ 0`), it has no integer root. -/
theorem no_int_root_of_quadHasRootMod_eq_false {b c : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : quadHasRootMod b c ℓ = false) (u : ℤ) : quadEval b c u ≠ 0 := by
  rw [quadHasRootMod_eq _ _ hℓ] at h
  exact no_int_root_of_anyBelow hℓ (quadEval_modEq (ℓ : ℤ)) h u

open Polynomial in
/-- If the monic integer quadratic `u² + b u + c` has no integer root, then it has no *rational*
root: by the rational root theorem, a rational root of a monic integer polynomial is an integer. -/
theorem no_rat_root_of_quadHasRootMod_eq_false {b c : ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : quadHasRootMod b c ℓ = false) (x : ℚ)
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
  refine no_int_root_of_quadHasRootMod_eq_false hℓ h z ?_
  have hQ : ((quadEval b c z : ℤ) : ℚ) = 0 := by
    simp only [quadEval]
    push_cast
    grind
  exact_mod_cast hQ

end ECCompute
