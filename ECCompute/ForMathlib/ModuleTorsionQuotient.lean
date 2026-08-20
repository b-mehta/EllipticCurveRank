/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Torsion, quotients and rank of modules over a product

Module-theoretic facts about torsion submodules, quotients by a product submodule, and the free
rank of a product: the cardinality of a finite `𝔽₂`-vector space, transport of the range of a
scalar multiple and of the torsion along a linear equivalence, the splitting of a quotient of a
binary product, and the free rank of a product with a finite factor.

## Main results

* `Module.natCard_eq_two_pow_finrank`: a finite `𝔽₂`-vector space has `2 ^ dimension` elements.
* `LinearEquiv.map_range_lsmul`, `LinearEquiv.map_torsionBy`: transport of the range of doubling
  and of the `2`-torsion along a `ℤ`-linear equivalence.
* `Submodule.prodQuotEquiv`: `(M × N) ⧸ (P.prod Q) ≃ₗ (M ⧸ P) × (N ⧸ Q)`.
* `Submodule.prodSubtypeEquiv`: `↥(S.prod T) ≃ ↥S × ↥T`.
* `Module.finrank_prod_finite`: `finrank ℤ (F × D) = finrank ℤ F` for a finite `D`.
-/

open Module

namespace Module

/-- A finite `𝔽₂`-vector space has cardinality `2 ^ dimension`. -/
lemma natCard_eq_two_pow_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ finrank (ZMod 2) V := by
  have := Module.Finite.of_finite (R := ZMod 2) (M := V)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- A finite `ℤ`-module has free rank zero. -/
lemma finrank_int_zero_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    finrank ℤ D = 0 := by
  have : Module.Finite ℤ D := Module.Finite.of_finite
  rw [Module.finrank_eq_zero_iff_isTorsion, ← isAddTorsion_iff_isTorsion_int]
  exact isAddTorsion_of_finite

/-- Adjoining a finite summand does not change the free rank. -/
lemma finrank_prod_finite (F : Type*) [AddCommGroup F] [Module.Finite ℤ F]
    (D : Type*) [AddCommGroup D] [Finite D] :
    finrank ℤ (F × D) = finrank ℤ F := by
  have hkerD : finrank ℤ (LinearMap.ker (LinearMap.fst ℤ F D)) = 0 := by
    rw [LinearMap.ker_fst, ← (LinearEquiv.ofInjective (LinearMap.inr ℤ F D)
      LinearMap.inr_injective).finrank_eq, finrank_int_zero_of_finite]
  have key := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.fst ℤ F D))
  rw [hkerD, add_zero,
    (LinearMap.quotKerEquivOfSurjective _ LinearMap.fst_surjective).finrank_eq] at key
  exact key.symm

end Module

namespace LinearEquiv

variable {H K : Type*} [AddCommGroup H] [AddCommGroup K]

/-- A linear equivalence carries the range of doubling to the range of doubling. -/
lemma map_range_lsmul (e : H ≃ₗ[ℤ] K) :
    (LinearMap.range (LinearMap.lsmul ℤ H 2)).map (e : H →ₗ[ℤ] K) =
      LinearMap.range (LinearMap.lsmul ℤ K 2) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by rw [map_smul]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(2 : ℤ) • e.symm w, ⟨e.symm w, rfl⟩, by rw [map_smul, e.apply_symm_apply]⟩

/-- A linear equivalence carries 2-torsion to 2-torsion. -/
lemma map_torsionBy (e : H ≃ₗ[ℤ] K) :
    (Submodule.torsionBy ℤ H 2).map (e : H →ₗ[ℤ] K) = Submodule.torsionBy ℤ K 2 := by
  ext z
  simp only [Submodule.mem_map, Submodule.mem_torsionBy_iff, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_smul, hy, map_zero]
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    rw [← map_smul, hz, map_zero]

end LinearEquiv

namespace Submodule

variable {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The quotient of a binary product by a product submodule splits as a product of quotients. -/
def prodQuotEquiv (P : Submodule R M) (Q : Submodule R N) :
    HasQuotient.Quotient (M × N) (P.prod Q) ≃ₗ[R] (M ⧸ P) × (N ⧸ Q) := by
  refine LinearEquiv.ofLinearMap
    ((P.prod Q).liftQ (LinearMap.prodMap P.mkQ Q.mkQ) ?_)
    (LinearMap.coprod
      (P.liftQ ((P.prod Q).mkQ.comp (LinearMap.inl R M N)) ?_)
      (Q.liftQ ((P.prod Q).mkQ.comp (LinearMap.inr R M N)) ?_)) ?_ ?_
  · intro z hz
    simpa [LinearMap.mem_ker, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod]
      using hz
  · intro x hx
    simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod, hx]
  · intro y hy
    simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod, hy]
  · apply LinearMap.ext
    rintro ⟨a, b⟩
    induction a using Submodule.Quotient.induction_on with | H x =>
    induction b using Submodule.Quotient.induction_on with | H y =>
    simp [← Submodule.Quotient.mk_add]
  · apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with | H xy =>
    obtain ⟨x, y⟩ := xy
    simp [← Submodule.Quotient.mk_add]

/-- The subtype of a product submodule is the product of the subtypes. -/
def prodSubtypeEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (S : Submodule ℤ M) (T : Submodule ℤ N) : ↥(S.prod T) ≃ ↥S × ↥T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Submodule
