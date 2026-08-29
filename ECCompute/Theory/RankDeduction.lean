/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

import ECCompute.ForMathlib.ModuleTorsionQuotient
import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# The rank-bound deduction (abstract core)

The group-theoretic core of the rank-bound descent argument, for a finitely generated
additive abelian group `H` as a `ℤ`-module.

Write `H ⧸ 2H` for `ModN H 2` (the quotient of `H` by its doubles, a `ZMod 2`-vector space) and
`H[2] = Submodule.torsionBy ℤ H 2` for the 2-torsion. The cardinality identity
`|H ⧸ nH| = n ^ rank H · |H[n]|` lives in `ECCompute.ForMathlib.ModuleTorsionQuotient`
(`ModN.natCard_modN`).

## Main results

* `RankDeduction.rank_ge_le`: `ρ ≤ rank H + t` when `Nat.card H[2] ≤ 2 ^ t` and `ρ` group
  elements have `𝔽₂`-linearly independent images under a descent-character hom
  `φ : H →+ (Fin ρ → ZMod 2)`, the form the certificate uses.

An invertible `ρ × ρ` matrix over `𝔽₂` supplies the linear-independence hypothesis.
-/

open Module ModN

namespace RankDeduction

variable {H : Type*} [AddCommGroup H] {ρ : ℕ}

/-- If `ρ` group elements have `𝔽₂`-linearly independent images under an additive hom
`φ : H →+ (Fin ρ → ZMod 2)`, then `H ⧸ 2H` has dimension at least `ρ`. (The hom automatically
factors through `H ⧸ 2H`, since the target has characteristic 2.) -/
theorem ρ_le_finrank_modN_two [Module.Finite ℤ H] (g : Fin ρ → H)
    (φ : H →+ (Fin ρ → ZMod 2)) (hindep : LinearIndependent (ZMod 2) (fun i ↦ φ (g i))) :
    ρ ≤ finrank (ZMod 2) (ModN H 2) := by
  have hφ : ∀ h, (2 : ℕ) • φ h = 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  set ψ : ModN H 2 →ₗ[ZMod 2] (Fin ρ → ZMod 2) := ModN.liftEquiv'.symm ⟨φ, hφ⟩
  have hψ : ∀ x, ψ (ModN.mkQ 2 x) = φ x := fun x ↦ rfl
  have hmk : LinearIndependent (ZMod 2) (fun i ↦ ModN.mkQ 2 (g i)) :=
    LinearIndependent.of_comp ψ (by simpa only [Function.comp_def, hψ] using hindep)
  simpa using hmk.fintype_card_le_finrank

/-- From `|H[2]| ≤ 2 ^ t` and `ρ` group elements whose images under `φ` are `𝔽₂`-linearly
independent, `ρ ≤ rank H + t`. This is the form the certificate uses. -/
public theorem rank_ge_le [Module.Finite ℤ H] {t : ℕ} (g : Fin ρ → H) (φ : H →+ (Fin ρ → ZMod 2))
    (hindep : LinearIndependent (ZMod 2) (fun i ↦ φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H 2) ≤ 2 ^ t) :
    ρ ≤ finrank ℤ H + t := by
  have h1 : ρ ≤ finrank (ZMod 2) (ModN H 2) := ρ_le_finrank_modN_two g φ hindep
  have key := natCard_modN (H := H) (n := 2)
  rw [natCard_eq_two_pow_finrank] at key
  have hmono : (2 : ℕ) ^ ρ ≤ 2 ^ (finrank ℤ H + t) :=
    calc (2 : ℕ) ^ ρ ≤ 2 ^ finrank (ZMod 2) (ModN H 2) := Nat.pow_le_pow_right (by norm_num) h1
      _ = 2 ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H 2) := key
      _ ≤ 2 ^ finrank ℤ H * 2 ^ t := Nat.mul_le_mul_left _ ht
      _ = 2 ^ (finrank ℤ H + t) := (pow_add 2 _ _).symm
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hmono

end RankDeduction
