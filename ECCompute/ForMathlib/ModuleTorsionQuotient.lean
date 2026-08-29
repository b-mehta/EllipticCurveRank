/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.ModN

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.DFinsupp.FiniteInfinite

/-!
# Torsion, quotients and rank of modules over a product

Module-theoretic facts about torsion submodules, quotients by a product submodule, and the free
rank of a product: the cardinality of a finite `𝔽₂`-vector space, transport of the range of a
scalar multiple and of the torsion along a linear equivalence, the splitting of a quotient of a
binary product, and the free rank of a product with a finite factor.

## Main results

* `Module.natCard_eq_two_pow_finrank`: a finite `𝔽₂`-vector space has `2 ^ dimension` elements.
* `LinearEquiv.map_range_lsmul`, `LinearEquiv.map_torsionBy`: transport of the range of `a • ·`
  and of the `a`-torsion along an `R`-linear equivalence.
* `Submodule.prodQuotEquiv`: `(M × N) ⧸ (P.prod Q) ≃ₗ (M ⧸ P) × (N ⧸ Q)`.
* `Submodule.prodSubtypeEquiv`: `↥(S.prod T) ≃ ↥S × ↥T`.
* `Submodule.range_lsmul_prod`, `Submodule.torsionBy_prod`, `Submodule.natCard_torsionBy_prod`:
  the range of `a • ·` and the `a`-torsion of a binary product split over the factors.
* `Module.finrank_prod_finite`: `finrank ℤ (F × D) = finrank ℤ F` for a finite `D`.
* `ModN.natCard_modN`: `|H ⧸ nH| = n ^ rank H · |H[n]|` for a finitely generated abelian group.
-/

section

open Module

namespace Module

/-- A finite `𝔽₂`-vector space has cardinality `2 ^ dimension`. -/
public lemma natCard_eq_two_pow_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] :
    Nat.card V = 2 ^ finrank (ZMod 2) V := by
  rw [natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- A finite `ℤ`-module has free rank zero. -/
lemma finrank_int_zero_of_finite {D : Type*} [AddCommGroup D] [Finite D] : finrank ℤ D = 0 := by
  have : Module.Finite ℤ D := Module.Finite.of_finite
  rw [finrank_eq_zero_iff_isTorsion, ← isAddTorsion_iff_isTorsion_int]
  exact isAddTorsion_of_finite

/-- The free rank of `F × D` equals that of `F` when `D` is finite. -/
public lemma finrank_prod_finite {F : Type*} [AddCommGroup F] [Module.Finite ℤ F]
    {D : Type*} [AddCommGroup D] [Finite D] :
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

variable {R : Type*} [CommRing R] {H K : Type*} [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K]

/-- A linear equivalence carries the range of `a • ·` to the range of `a • ·`. -/
public lemma map_range_lsmul (e : H ≃ₗ[R] K) (a : R) :
    (LinearMap.range (LinearMap.lsmul R H a)).map (e : H →ₗ[R] K) =
      LinearMap.range (LinearMap.lsmul R K a) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by rw [map_smul]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨a • e.symm w, ⟨e.symm w, rfl⟩, by rw [map_smul, e.apply_symm_apply]⟩

/-- A linear equivalence carries `a`-torsion to `a`-torsion. -/
public lemma map_torsionBy (e : H ≃ₗ[R] K) (a : R) :
    (Submodule.torsionBy R H a).map (e : H →ₗ[R] K) = Submodule.torsionBy R K a := by
  ext z
  simp only [Submodule.mem_map, Submodule.mem_torsionBy_iff, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_smul, hy, map_zero]
  · exact fun hz ↦ ⟨e.symm z, by rw [← map_smul, hz, map_zero], by simp⟩

end LinearEquiv

namespace Submodule

variable {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The quotient of a binary product by a product submodule splits as a product of quotients. -/
public def prodQuotEquiv (P : Submodule R M) (Q : Submodule R N) :
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
public def prodSubtypeEquiv (S : Submodule R M) (T : Submodule R N) : ↥(S.prod T) ≃ ↥S × ↥T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `a • ·` has range the product of the ranges of the coordinate maps. -/
public lemma range_lsmul_prod {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a : R) :
    LinearMap.range (LinearMap.lsmul R (M × N) a) =
      (LinearMap.range (LinearMap.lsmul R M a)).prod (LinearMap.range (LinearMap.lsmul R N a)) := by
  have h : LinearMap.lsmul R (M × N) a =
      LinearMap.prodMap (LinearMap.lsmul R M a) (LinearMap.lsmul R N a) := by
    ext p <;> simp [LinearMap.lsmul_apply]
  rw [h, LinearMap.range_prodMap]

/-- The `a`-torsion of a product is the product of the `a`-torsions. -/
public lemma torsionBy_prod {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a : R) :
    Submodule.torsionBy R (M × N) a =
      (Submodule.torsionBy R M a).prod (Submodule.torsionBy R N a) := by
  ext ⟨x, y⟩
  simp [Submodule.mem_torsionBy_iff, Submodule.mem_prod, Prod.smul_mk, Prod.ext_iff]

/-- `Nat.card` of the `a`-torsion of a product multiplies over the factors. -/
public lemma natCard_torsionBy_prod {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (a : R) :
    Nat.card (Submodule.torsionBy R (M × N) a) =
      Nat.card (Submodule.torsionBy R M a) * Nat.card (Submodule.torsionBy R N a) := by
  rw [torsionBy_prod, ← Nat.card_prod]
  exact Nat.card_congr (prodSubtypeEquiv _ _)

end Submodule

namespace ModN

variable {H : Type*} [AddCommGroup H] {n : ℕ}

/-- The `n`-torsion `H[n]` is the kernel of the map `x ↦ n • x`. -/
lemma torsionBy_eq_ker : Submodule.torsionBy ℤ H n = LinearMap.ker (LinearMap.lsmul ℤ H n) := rfl

theorem isAddTorsion [NeZero n] : IsAddTorsion (ModN H n) := by
  intro x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨n, NeZero.pos _, by simp [← Nat.cast_smul_eq_nsmul (ZMod n)]⟩

public instance [NeZero n] [Module.Finite ℤ H] : Finite (ModN H n) :=
  Module.finite_of_fg_torsion (ModN H n) (isAddTorsion_iff_isTorsion_int.1 isAddTorsion)

public instance [NeZero n] [Module.Finite ℤ H] : Module.Finite (ZMod n) (ModN H n) :=
  Module.Finite.of_finite

public instance [NeZero n] [Module.Finite ℤ H] : Finite (Submodule.torsionBy ℤ H n) :=
  Module.finite_of_fg_torsion _
    (Submodule.torsionBy_isTorsion_nonZeroDivisor _ (by simp [NeZero.ne]))

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
  grind

variable {K : Type*} [AddCommGroup K]

/-- `Nat.card (H ⧸ nH)` is invariant under linear equivalences. -/
lemma natCard_modN_congr (e : H ≃ₗ[ℤ] K) : Nat.card (ModN H n) = Nat.card (ModN K n) :=
  Nat.card_congr (Submodule.Quotient.equiv _ _ e (e.map_range_lsmul n)).toEquiv

/-- `Nat.card H[n]` is invariant under linear equivalences. -/
lemma natCard_torsionBy_congr (e : H ≃ₗ[ℤ] K) :
    Nat.card (Submodule.torsionBy ℤ H n) = Nat.card (Submodule.torsionBy ℤ K n) := by
  rw [← e.map_torsionBy]
  exact Nat.card_congr (e.submoduleMap (Submodule.torsionBy ℤ H n)).toEquiv

section Prod

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- `H ⧸ nH` for a product is the product of the factors' `H ⧸ nH`. -/
lemma natCard_modN_prod :
    Nat.card (ModN (M × N) n) = Nat.card (ModN M n) * Nat.card (ModN N n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    (((Submodule.quotEquivOfEq _ _ (Submodule.range_lsmul_prod (n : ℤ))).toEquiv).trans
      (Submodule.prodQuotEquiv _ _).toEquiv)

end Prod

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
  rw [natCard_modN_prod, Submodule.natCard_torsionBy_prod, ModN.natCard_eq F n,
    natCard_modN_of_finite D, natCard_torsionBy_eq_one_of_noZeroSMul F, one_mul]

/-- For a finitely generated abelian group `H`, `|H ⧸ nH| = n ^ rank H · |H[n]|`. -/
public theorem natCard_modN [NeZero n] [Module.Finite ℤ H] :
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

end ModN

end
