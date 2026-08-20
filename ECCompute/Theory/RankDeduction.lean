/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-!
# The rank-bound deduction (abstract core)

The group-theoretic core of the rank-bound descent argument, phrased for a finitely generated
additive abelian group `H` as a `ℤ`-module, with no reference to the elliptic curve or the
`𝔽₂`-invertibility check.

Write `H ⧸ 2H` for `ModN H 2` (the quotient of `H` by its doubles, a `ZMod 2`-vector space) and
`H[2] = Submodule.torsionBy ℤ H 2` for the 2-torsion.

## Main results

* `RankDeduction.natCard_modN_two`: the cardinality identity
  `Nat.card (ModN H 2) = 2 ^ finrank ℤ H * Nat.card H[2]`.
* `RankDeduction.finrank_modN_two`: the dimension formula
  `dim_{𝔽₂}(H ⧸ 2H) = rank H + dim_{𝔽₂} H[2]`.
* `RankDeduction.rho_le_finrank_modN_two`: if `ρ` elements have `𝔽₂`-linearly independent images
  under some additive hom `φ : H →+ (Fin ρ → ZMod 2)`, then `ρ ≤ dim_{𝔽₂}(H ⧸ 2H)`.
* `RankDeduction.rank_ge`: the packaged deduction, `ρ ≤ rank H + t` whenever `Nat.card H[2] = 2 ^ t`
  and there are `ρ` independent descent-character values, i.e. `rank H ≥ ρ - t`.

An invertible `ρ × ρ` matrix over `𝔽₂` supplies the linear-independence hypothesis.
-/

open Module

namespace RankDeduction

/-- A finite `𝔽₂`-vector space has cardinality `2 ^ dimension`. -/
lemma natCard_eq_two_pow_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ finrank (ZMod 2) V := by
  have := Module.Finite.of_finite (R := ZMod 2) (M := V)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

variable {H : Type*} [AddCommGroup H]

/-- Notation-free abbreviation for the 2-torsion subgroup as a `ℤ`-submodule. -/
local notation3 M "⟦2⟧" => Submodule.torsionBy ℤ M 2

/-! ### The 2-torsion as kernel of doubling -/

/-- The 2-torsion `H[2]` is the kernel of the doubling map `x ↦ 2 • x`. -/
lemma torsionBy_two_eq_ker :
    (Submodule.torsionBy ℤ H 2) = LinearMap.ker (LinearMap.lsmul ℤ H 2) := rfl

/-! ### Finiteness of `H ⧸ 2H` -/

/-- Doubling annihilates `ModN H 2`. -/
lemma two_zsmul_modN (x : ModN H 2) : (2 : ℤ) • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (LinearMap.lsmul ℤ H 2)) x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, by simp [LinearMap.lsmul_apply]⟩

instance instFiniteModN [Module.Finite ℤ H] : Finite (ModN H 2) := by
  have : Module.Finite ℤ (ModN H 2) := Module.Finite.quotient ℤ _
  exact Module.finite_of_fg_torsion (ModN H 2)
    (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, two_zsmul_modN x⟩)

instance instFiniteDimModN [Module.Finite ℤ H] : Module.Finite (ZMod 2) (ModN H 2) :=
  Module.Finite.of_finite

instance instFiniteTorsionBy [Module.Finite ℤ H] :
    Finite (Submodule.torsionBy ℤ H 2) :=
  Module.finite_of_fg_torsion _
    (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, Submodule.smul_torsionBy 2 x⟩)

/-! ### The cardinality identity for finite groups -/

/-- For a finite abelian group `D`, doubling has equally large kernel and cokernel:
`Nat.card (D ⧸ 2D) = Nat.card D[2]`. -/
lemma natCard_modN_two_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    Nat.card (ModN D 2) = Nat.card (Submodule.torsionBy ℤ D 2) := by
  set f := LinearMap.lsmul ℤ D 2
  have hquot : Nat.card (D ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h1 : Nat.card D = Nat.card (D ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    (LinearMap.ker f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  have h2 : Nat.card D = Nat.card (ModN D 2) * Nat.card (LinearMap.range f) :=
    (LinearMap.range f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  rw [torsionBy_two_eq_ker]
  have hpos : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0, by simp⟩, inferInstance⟩
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) ?_
  rw [mul_comm, ← h2, h1, hquot, mul_comm]

/-! ### Transport along `ℤ`-linear equivalences -/

variable {K : Type*} [AddCommGroup K]

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

/-- `Nat.card (H ⧸ 2H)` is invariant under linear equivalences. -/
lemma natCard_modN_two_congr (e : H ≃ₗ[ℤ] K) :
    Nat.card (ModN H 2) = Nat.card (ModN K 2) :=
  Nat.card_congr
    (Submodule.Quotient.equiv _ _ e (map_range_lsmul e)).toEquiv

/-- `Nat.card H[2]` is invariant under linear equivalences. -/
lemma natCard_torsionBy_two_congr (e : H ≃ₗ[ℤ] K) :
    Nat.card (Submodule.torsionBy ℤ H 2) = Nat.card (Submodule.torsionBy ℤ K 2) := by
  rw [← map_torsionBy e]
  exact Nat.card_congr (e.submoduleMap (Submodule.torsionBy ℤ H 2)).toEquiv

/-! ### Behaviour under binary products -/

section ProdQuot

variable {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The quotient of a binary product by a product submodule splits as a product of quotients.
Stated over a general ring to avoid the `ℤ`-module diamond on quotient types. -/
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

end ProdQuot

section Prod

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Doubling has range the product of the ranges of the coordinate doublings. -/
lemma range_lsmul_prod :
    LinearMap.range (LinearMap.lsmul ℤ (M × N) 2) =
      (LinearMap.range (LinearMap.lsmul ℤ M 2)).prod
        (LinearMap.range (LinearMap.lsmul ℤ N 2)) := by
  have h : LinearMap.lsmul ℤ (M × N) 2 =
      LinearMap.prodMap (LinearMap.lsmul ℤ M 2) (LinearMap.lsmul ℤ N 2) := by
    ext p <;> simp [LinearMap.lsmul_apply]
  rw [h, LinearMap.range_prodMap]

/-- `H ⧸ 2H` for a product is the product of the factors' `H ⧸ 2H`. -/
lemma natCard_modN_two_prod :
    Nat.card (ModN (M × N) 2) = Nat.card (ModN M 2) * Nat.card (ModN N 2) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    (((Submodule.quotEquivOfEq _ _ range_lsmul_prod).toEquiv).trans (prodQuotEquiv _ _).toEquiv)

/-- The 2-torsion of a product is the product of the 2-torsions. -/
lemma torsionBy_two_prod :
    Submodule.torsionBy ℤ (M × N) 2 =
      (Submodule.torsionBy ℤ M 2).prod (Submodule.torsionBy ℤ N 2) := by
  ext ⟨a, b⟩
  simp [Submodule.mem_torsionBy_iff, Submodule.mem_prod, Prod.smul_mk, Prod.ext_iff]

/-- The subtype of a product submodule is the product of the subtypes. -/
def prodSubtypeEquiv (S : Submodule ℤ M) (T : Submodule ℤ N) : ↥(S.prod T) ≃ ↥S × ↥T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `H[2]` for a product is the product of the factors' `H[2]`. -/
lemma natCard_torsionBy_two_prod :
    Nat.card (Submodule.torsionBy ℤ (M × N) 2) =
      Nat.card (Submodule.torsionBy ℤ M 2) * Nat.card (Submodule.torsionBy ℤ N 2) := by
  rw [torsionBy_two_prod, ← Nat.card_prod]
  exact Nat.card_congr (prodSubtypeEquiv _ _)

end Prod

/-! ### The cardinality identity for finitely generated groups -/

/-- A finite `ℤ`-module has free rank zero. -/
lemma finrank_int_zero_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    finrank ℤ D = 0 := by
  have : Module.Finite ℤ D := Module.Finite.of_finite
  rw [Module.finrank_eq_zero_iff_isTorsion, ← isAddTorsion_iff_isTorsion_int]
  exact isAddTorsion_of_finite

/-- A torsion-free module has trivial 2-torsion. -/
lemma natCard_torsionBy_two_eq_one_of_noZeroSMul (F : Type*) [AddCommGroup F]
    [NoZeroSMulDivisors ℤ F] : Nat.card (Submodule.torsionBy ℤ F 2) = 1 := by
  have hbot : Submodule.torsionBy ℤ F 2 = ⊥ :=
    (isSMulRegular_iff_torsionBy_eq_bot F 2).1 (smul_right_injective F two_ne_zero)
  rw [hbot]
  exact Nat.card_unique

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

/-- The identity for a free-times-finite decomposition. -/
lemma natCard_modN_two_of_free_prod_finite
    (F : Type*) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] [NoZeroSMulDivisors ℤ F]
    (D : Type*) [AddCommGroup D] [Finite D] :
    Nat.card (ModN (F × D) 2) =
      2 ^ finrank ℤ F * Nat.card (Submodule.torsionBy ℤ (F × D) 2) := by
  rw [natCard_modN_two_prod, natCard_torsionBy_two_prod, ModN.natCard_eq F 2,
    natCard_modN_two_of_finite D, natCard_torsionBy_two_eq_one_of_noZeroSMul F, one_mul]

/-- For a finitely generated abelian group `H`, `|H ⧸ 2H| = 2 ^ rank H · |H[2]|`. -/
theorem natCard_modN_two [Module.Finite ℤ H] :
    Nat.card (ModN H 2) = 2 ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H 2) := by
  obtain ⟨n, ι, fι, p, hp, ee, ⟨iso⟩⟩ := Module.equiv_free_prod_directSum ℤ H
  set D := DirectSum ι fun i => ℤ ⧸ (ℤ ∙ p i ^ ee i)
  have : ∀ i, NeZero (p i ^ ee i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : ∀ i, Finite (ℤ ⧸ (ℤ ∙ (p i ^ ee i))) := fun i =>
    inferInstanceAs (Finite (ℤ ⧸ Ideal.span {p i ^ ee i}))
  have : Finite D := by
    classical
    have : ∀ i, Fintype (ℤ ⧸ (ℤ ∙ p i ^ ee i)) := fun i => Fintype.ofFinite _
    exact Finite.of_equiv _ (DFinsupp.equivFunOnFintype).symm
  have hfrH : finrank ℤ H = finrank ℤ (Fin n →₀ ℤ) := by
    rw [iso.finrank_eq]
    exact finrank_prod_finite _ _
  calc Nat.card (ModN H 2)
      = Nat.card (ModN ((Fin n →₀ ℤ) × D) 2) := natCard_modN_two_congr iso
    _ = 2 ^ finrank ℤ (Fin n →₀ ℤ) *
          Nat.card (Submodule.torsionBy ℤ ((Fin n →₀ ℤ) × D) 2) :=
        natCard_modN_two_of_free_prod_finite _ _
    _ = 2 ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H 2) := by
        rw [hfrH, natCard_torsionBy_two_congr iso]

/-- For a finitely generated abelian group `H` whose 2-torsion has cardinality `2 ^ t`,
`|H ⧸ 2H| = 2 ^ (rank H + t)`. -/
theorem natCard_modN_two_pow [Module.Finite ℤ H] {t : ℕ}
    (ht : Nat.card (Submodule.torsionBy ℤ H 2) = 2 ^ t) :
    Nat.card (ModN H 2) = 2 ^ (finrank ℤ H + t) := by
  rw [natCard_modN_two, ht, ← pow_add]

/-! ### The dimension identity -/

/-- For a finitely generated abelian group `H`, `dim_{𝔽₂}(H ⧸ 2H) = rank H + dim_{𝔽₂} H[2]`, where
the 2-torsion carries its `ZMod 2`-module structure. -/
theorem finrank_modN_two [Module.Finite ℤ H] :
    let : Module (ZMod 2) (Submodule.torsionBy ℤ H 2) := AddSubgroup.torsionBy.zmodModule
    finrank (ZMod 2) (ModN H 2) =
      finrank ℤ H + finrank (ZMod 2) (Submodule.torsionBy ℤ H 2) := by
  let : Module (ZMod 2) (Submodule.torsionBy ℤ H 2) := AddSubgroup.torsionBy.zmodModule
  have key := natCard_modN_two_pow (natCard_eq_two_pow_finrank (Submodule.torsionBy ℤ H 2))
  rw [natCard_eq_two_pow_finrank (ModN H 2)] at key
  exact Nat.pow_right_injective (le_refl 2) key

/-! ### The deduction -/

variable {ρ : ℕ}

/-- If `ρ` group elements have `𝔽₂`-linearly independent images under an additive hom
`φ : H →+ (Fin ρ → ZMod 2)`, then `H ⧸ 2H` has dimension at least `ρ`. (The hom automatically
factors through `H ⧸ 2H`, since the target has characteristic 2.) -/
theorem rho_le_finrank_modN_two [Module.Finite ℤ H] (g : Fin ρ → H)
    (φ : H →+ (Fin ρ → ZMod 2))
    (hindep : LinearIndependent (ZMod 2) (fun i => φ (g i))) :
    ρ ≤ finrank (ZMod 2) (ModN H 2) := by
  have hφ : ∀ h, (2 : ℕ) • φ h = 0 := fun h => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  set ψ : ModN H 2 →ₗ[ZMod 2] (Fin ρ → ZMod 2) := ModN.liftEquiv'.symm ⟨φ, hφ⟩
  have hψ : ∀ x, ψ (ModN.mkQ 2 x) = φ x := fun x => rfl
  have hmk : LinearIndependent (ZMod 2) (fun i => ModN.mkQ 2 (g i)) :=
    LinearIndependent.of_comp ψ (by simpa only [Function.comp_def, hψ] using hindep)
  simpa using hmk.fintype_card_le_finrank

/-- If `ρ` group elements have `𝔽₂`-linearly independent images under a descent-character tuple
`φ`, and the 2-torsion has cardinality `2 ^ t`, then `rank H ≥ ρ - t` (stated as
`ρ ≤ rank H + t`). -/
theorem rank_ge [Module.Finite ℤ H] {t : ℕ} (g : Fin ρ → H) (φ : H →+ (Fin ρ → ZMod 2))
    (hindep : LinearIndependent (ZMod 2) (fun i => φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H 2) = 2 ^ t) :
    ρ ≤ finrank ℤ H + t := by
  have h1 : ρ ≤ finrank (ZMod 2) (ModN H 2) := rho_le_finrank_modN_two g φ hindep
  have key := natCard_modN_two_pow ht
  rw [natCard_eq_two_pow_finrank (ModN H 2)] at key
  have h2 : finrank (ZMod 2) (ModN H 2) = finrank ℤ H + t :=
    Nat.pow_right_injective (le_refl 2) key
  lia

/-- The bound with only an *upper* bound on the 2-torsion: if `ρ` group elements have
`𝔽₂`-linearly independent images under `φ`, and `|H[2]| ≤ 2 ^ t`, then `ρ ≤ rank H + t`. This is
what a certificate needs when it concedes `t` torsion dimensions without pinning down the exact
2-torsion of the generated subgroup. -/
theorem rank_ge_le [Module.Finite ℤ H] {t : ℕ} (g : Fin ρ → H) (φ : H →+ (Fin ρ → ZMod 2))
    (hindep : LinearIndependent (ZMod 2) (fun i => φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H 2) ≤ 2 ^ t) :
    ρ ≤ finrank ℤ H + t := by
  have h1 : ρ ≤ finrank (ZMod 2) (ModN H 2) := rho_le_finrank_modN_two g φ hindep
  have key := natCard_modN_two (H := H)
  rw [natCard_eq_two_pow_finrank (ModN H 2)] at key
  have hmono : (2 : ℕ) ^ ρ ≤ 2 ^ (finrank ℤ H + t) :=
    calc (2 : ℕ) ^ ρ ≤ 2 ^ finrank (ZMod 2) (ModN H 2) := Nat.pow_le_pow_right (by norm_num) h1
      _ = 2 ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H 2) := key
      _ ≤ 2 ^ finrank ℤ H * 2 ^ t := Nat.mul_le_mul_left _ ht
      _ = 2 ^ (finrank ℤ H + t) := (pow_add 2 _ _).symm
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hmono

end RankDeduction
