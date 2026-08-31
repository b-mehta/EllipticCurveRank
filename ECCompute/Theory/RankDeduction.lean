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
additive abelian group `H` as a `ℤ`-module and a prime `p`.

Write `H ⧸ pH` for `ModN H p` (the quotient of `H` by its `p`-th multiples, a `ZMod p`-vector
space) and `H[p] = Submodule.torsionBy ℤ H p` for the `p`-torsion. The cardinality identity
`|H ⧸ nH| = n ^ rank H · |H[n]|` lives in `ECCompute.ForMathlib.ModuleTorsionQuotient`
(`ModN.natCard_modN`).

## Main results

* `RankDeduction.rank_ge_le`: `ρ ≤ rank H + t` when `Nat.card H[p] ≤ p ^ t` and `ρ` group
  elements have linearly independent images under a descent-character hom
  `φ : H →+ (Fin ρ → ZMod p)`, the form the certificate uses at `p = 2`.

An invertible `ρ × ρ` matrix over `ZMod p` supplies the linear-independence hypothesis.
-/

open Module ModN

namespace RankDeduction

variable {H : Type*} [AddCommGroup H] {ρ p : ℕ} [Fact p.Prime]

/-- If `ρ` group elements have linearly independent images under an additive hom
`φ : H →+ (Fin ρ → ZMod p)`, then `H ⧸ pH` has dimension at least `ρ`. (The hom automatically
factors through `H ⧸ pH`, since the target has characteristic `p`.) -/
theorem ρ_le_finrank_modN [Module.Finite ℤ H] (g : Fin ρ → H)
    (φ : H →+ (Fin ρ → ZMod p)) (hindep : LinearIndependent (ZMod p) (fun i ↦ φ (g i))) :
    ρ ≤ finrank (ZMod p) (ModN H p) := by
  have hφ : ∀ h, p • φ h = 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  set ψ : ModN H p →ₗ[ZMod p] (Fin ρ → ZMod p) := ModN.liftEquiv'.symm ⟨φ, hφ⟩
  have hψ : ∀ x, ψ (ModN.mkQ p x) = φ x := fun x ↦ rfl
  have hmk : LinearIndependent (ZMod p) (fun i ↦ ModN.mkQ p (g i)) :=
    LinearIndependent.of_comp ψ (by simpa only [Function.comp_def, hψ] using hindep)
  simpa using hmk.fintype_card_le_finrank

/-- From `|H[p]| ≤ p ^ t` and `ρ` group elements whose images under `φ` are linearly
independent, `ρ ≤ rank H + t`. This is the form the certificate uses at `p = 2`. -/
public theorem rank_ge_le [Module.Finite ℤ H] {t : ℕ} (g : Fin ρ → H) (φ : H →+ (Fin ρ → ZMod p))
    (hindep : LinearIndependent (ZMod p) (fun i ↦ φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H p) ≤ p ^ t) :
    ρ ≤ finrank ℤ H + t := by
  have h1 : ρ ≤ finrank (ZMod p) (ModN H p) := ρ_le_finrank_modN g φ hindep
  have key := natCard_modN (H := H) (n := p)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at key
  have hmono : p ^ ρ ≤ p ^ (finrank ℤ H + t) :=
    calc p ^ ρ ≤ p ^ finrank (ZMod p) (ModN H p) :=
        Nat.pow_le_pow_right (Fact.out : p.Prime).pos h1
      _ = p ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H p) := key
      _ ≤ p ^ finrank ℤ H * p ^ t := Nat.mul_le_mul_left _ ht
      _ = p ^ (finrank ℤ H + t) := (pow_add p _ _).symm
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hmono

end RankDeduction
