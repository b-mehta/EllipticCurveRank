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
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.DFinsupp.FiniteInfinite

/-!
# The rank-bound deduction (abstract core)

The group-theoretic core of the rank-bound descent argument, for a finitely generated
additive abelian group `H` as a `ℤ`-module.

Write `H ⧸ 2H` for `ModN H 2` (the quotient of `H` by its doubles, a `ZMod 2`-vector space) and
`H[2] = Submodule.torsionBy ℤ H 2` for the 2-torsion.

## Main results

* `RankDeduction.rank_ge_le`: `ρ ≤ rank H + t` when `Nat.card H[2] ≤ 2 ^ t` and `ρ` group
  elements have `𝔽₂`-linearly independent images under a descent-character hom
  `φ : H →+ (Fin ρ → ZMod 2)`, the form the certificate uses.

An invertible `ρ × ρ` matrix over `𝔽₂` supplies the linear-independence hypothesis.
-/

open Module

namespace RankDeduction

variable {H : Type*} [AddCommGroup H]

/-! ### The `n`-torsion as kernel of `n • ·` -/

variable {n : ℕ}

/-- The `n`-torsion `H[n]` is the kernel of the map `x ↦ n • x`. -/
lemma torsionBy_eq_ker : Submodule.torsionBy ℤ H n = LinearMap.ker (LinearMap.lsmul ℤ H n) := rfl

/-! ### Finiteness of `H ⧸ nH` -/

theorem ModN.isAddTorsion [NeZero n] : IsAddTorsion (ModN H n) := by
  intro x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨n, NeZero.pos _, by simp [← Nat.cast_smul_eq_nsmul (ZMod n)]⟩

instance [NeZero n] [Module.Finite ℤ H] : Finite (ModN H n) :=
  Module.finite_of_fg_torsion (ModN H n) (isAddTorsion_iff_isTorsion_int.1 ModN.isAddTorsion)

instance [NeZero n] [Module.Finite ℤ H] : Module.Finite (ZMod n) (ModN H n) :=
  Module.Finite.of_finite

instance [NeZero n] [Module.Finite ℤ H] : Finite (Submodule.torsionBy ℤ H n) :=
  Module.finite_of_fg_torsion _
    (Submodule.torsionBy_isTorsion_nonZeroDivisor _ (by simp [NeZero.ne]))

/-! ### The cardinality identity for finite groups -/

/-- For a finite abelian group `D`, `x ↦ n • x` has equally large kernel and cokernel:
`Nat.card (D ⧸ nD) = Nat.card D[n]`. -/
lemma natCard_modN_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    Nat.card (ModN D n) = Nat.card (Submodule.torsionBy ℤ D n) := by
  set f := LinearMap.lsmul ℤ D (n : ℤ)
  have hquot : Nat.card (D ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h1 : Nat.card D = Nat.card (D ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    (LinearMap.ker f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  have h2 : Nat.card D = Nat.card (ModN D n) * Nat.card (LinearMap.range f) :=
    (LinearMap.range f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  rw [torsionBy_eq_ker]
  have hpos : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0, by simp⟩, inferInstance⟩
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) ?_
  rw [mul_comm, ← h2, h1, hquot, mul_comm]

/-! ### Transport along `ℤ`-linear equivalences -/

variable {K : Type*} [AddCommGroup K]

/-- `Nat.card (H ⧸ nH)` is invariant under linear equivalences. -/
lemma natCard_modN_congr (e : H ≃ₗ[ℤ] K) : Nat.card (ModN H n) = Nat.card (ModN K n) :=
  Nat.card_congr (Submodule.Quotient.equiv _ _ e (e.map_range_lsmul n)).toEquiv

/-- `Nat.card H[n]` is invariant under linear equivalences. -/
lemma natCard_torsionBy_congr (e : H ≃ₗ[ℤ] K) :
    Nat.card (Submodule.torsionBy ℤ H n) = Nat.card (Submodule.torsionBy ℤ K n) := by
  rw [← e.map_torsionBy]
  exact Nat.card_congr (e.submoduleMap (Submodule.torsionBy ℤ H n)).toEquiv

/-! ### Behaviour under binary products -/

section Prod

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- `x ↦ n • x` has range the product of the ranges of the coordinate maps. -/
lemma range_lsmul_prod :
    LinearMap.range (LinearMap.lsmul ℤ (M × N) (n : ℤ)) =
      (LinearMap.range (LinearMap.lsmul ℤ M (n : ℤ))).prod
        (LinearMap.range (LinearMap.lsmul ℤ N (n : ℤ))) := by
  have h : LinearMap.lsmul ℤ (M × N) (n : ℤ) =
      LinearMap.prodMap (LinearMap.lsmul ℤ M (n : ℤ)) (LinearMap.lsmul ℤ N (n : ℤ)) := by
    ext p <;> simp [LinearMap.lsmul_apply]
  rw [h, LinearMap.range_prodMap]

/-- `H ⧸ nH` for a product is the product of the factors' `H ⧸ nH`. -/
lemma natCard_modN_prod :
    Nat.card (ModN (M × N) n) = Nat.card (ModN M n) * Nat.card (ModN N n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    (((Submodule.quotEquivOfEq _ _ range_lsmul_prod).toEquiv).trans
      (Submodule.prodQuotEquiv _ _).toEquiv)

/-- The `n`-torsion of a product is the product of the `n`-torsions. -/
lemma torsionBy_prod :
    Submodule.torsionBy ℤ (M × N) n =
      (Submodule.torsionBy ℤ M n).prod (Submodule.torsionBy ℤ N n) := by
  ext ⟨a, b⟩
  simp [Submodule.mem_torsionBy_iff, Submodule.mem_prod, Prod.smul_mk, Prod.ext_iff]

/-- `H[n]` for a product is the product of the factors' `H[n]`. -/
lemma natCard_torsionBy_prod :
    Nat.card (Submodule.torsionBy ℤ (M × N) n) =
      Nat.card (Submodule.torsionBy ℤ M n) * Nat.card (Submodule.torsionBy ℤ N n) := by
  rw [torsionBy_prod, ← Nat.card_prod]
  exact Nat.card_congr (Submodule.prodSubtypeEquiv _ _)

end Prod

/-! ### The cardinality identity for finitely generated groups -/

/-- A torsion-free module has trivial `n`-torsion. -/
lemma natCard_torsionBy_eq_one_of_noZeroSMul [NeZero n] (F : Type*) [AddCommGroup F]
    [NoZeroSMulDivisors ℤ F] : Nat.card (Submodule.torsionBy ℤ F n) = 1 := by
  rw [(isSMulRegular_iff_torsionBy_eq_bot F (n : ℤ)).1
    (smul_right_injective F (by simp [NeZero.ne]))]
  exact Nat.card_unique

/-- The identity for a free-times-finite decomposition. -/
lemma natCard_modN_of_free_prod_finite [NeZero n]
    {F : Type*} [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] [NoZeroSMulDivisors ℤ F]
    {D : Type*} [AddCommGroup D] [Finite D] :
    Nat.card (ModN (F × D) n) =
      n ^ finrank ℤ F * Nat.card (Submodule.torsionBy ℤ (F × D) n) := by
  rw [natCard_modN_prod, natCard_torsionBy_prod, ModN.natCard_eq F n,
    natCard_modN_of_finite D, natCard_torsionBy_eq_one_of_noZeroSMul F, one_mul]

/-- For a finitely generated abelian group `H`, `|H ⧸ nH| = n ^ rank H · |H[n]|`. -/
theorem natCard_modN [NeZero n] [Module.Finite ℤ H] :
    Nat.card (ModN H n) = n ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H n) := by
  obtain ⟨m, ι, fι, p, hp, ee, ⟨iso⟩⟩ := Module.equiv_free_prod_directSum ℤ H
  set D := DirectSum ι fun i ↦ ℤ ⧸ (ℤ ∙ p i ^ ee i)
  have : ∀ i, NeZero (p i ^ ee i) := fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : ∀ i, Finite (ℤ ⧸ (ℤ ∙ (p i ^ ee i))) := fun i ↦
    inferInstanceAs (Finite (ℤ ⧸ Ideal.span {p i ^ ee i}))
  have : Finite D := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  calc Nat.card (ModN H n)
      = Nat.card (ModN ((Fin m →₀ ℤ) × D) n) := natCard_modN_congr iso
    _ = n ^ finrank ℤ (Fin m →₀ ℤ) *
          Nat.card (Submodule.torsionBy ℤ ((Fin m →₀ ℤ) × D) n) :=
        natCard_modN_of_free_prod_finite
    _ = n ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H n) := by
        rw [iso.finrank_eq.trans finrank_prod_finite, natCard_torsionBy_congr iso]

/-! ### The deduction -/

variable {ρ : ℕ}

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
