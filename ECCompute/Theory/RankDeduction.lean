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
import Mathlib.Algebra.Algebra.ZMod
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

* `RankDeduction.rank_ge_le`: `Nat.card ι ≤ rank H + t` when `Nat.card H[p] ≤ p ^ t` and a
  finite family `g : ι → H` has linearly independent images under a descent-character hom
  `φ : H →+ (ι → F)`, for any field `F` of characteristic `p` (the certificate uses
  `p = 2` and `F = ZMod 2`).

An invertible matrix over `F` supplies the linear-independence hypothesis.
-/

open Module ModN

namespace RankDeduction

variable {ι H : Type*} [AddCommGroup H] [Module.Finite ℤ H] [Finite ι] {p : ℕ}
  {F : Type*} [Field F] [CharP F p]

/-- If a finite family `g : ι → H` has linearly independent images under an additive hom
`φ : H →+ (ι → F)` into a field `F` of characteristic `p`, then `H ⧸ pH` has dimension at
least `Nat.card ι`. (The hom automatically factors through `H ⧸ pH`, since the target has
characteristic `p`, and `F`-independence restricts to the prime subfield.) -/
theorem card_le_finrank_modN (hp : p.Prime) (g : ι → H)
    (φ : H →+ (ι → F)) (hindep : LinearIndependent F (fun i ↦ φ (g i))) :
    Nat.card ι ≤ finrank (ZMod p) (ModN H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ι := Fintype.ofFinite ι
  let _alg : Algebra (ZMod p) F := ZMod.algebra F p
  have hφ : ∀ h, p • φ h = 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  set ψ : ModN H p →ₗ[ZMod p] (ι → F) := ModN.liftEquiv'.symm ⟨φ, hφ⟩
  have hψ : ∀ x, ψ (ModN.mkQ p x) = φ x := fun x ↦ rfl
  have hmk : LinearIndependent (ZMod p) (fun i ↦ ModN.mkQ p (g i)) :=
    LinearIndependent.of_comp ψ (by
      simpa only [Function.comp_def, hψ] using hindep.restrict_scalars
        (by simpa [Algebra.smul_def] using (algebraMap (ZMod p) F).injective))
  simpa using hmk.fintype_card_le_finrank

/-- From `|H[p]| ≤ p ^ t` and a finite family of group elements whose images under `φ` are
linearly independent, `Nat.card ι ≤ rank H + t`. This is the form the certificate uses at
`p = 2`. -/
public theorem rank_ge_le (hp : p.Prime) {t : ℕ} (g : ι → H)
    (φ : H →+ (ι → F)) (hindep : LinearIndependent F (fun i ↦ φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H p) ≤ p ^ t) :
    Nat.card ι ≤ finrank ℤ H + t := by
  have : Fact p.Prime := ⟨hp⟩
  grw [card_le_finrank_modN hp g φ hindep, ← Nat.pow_le_pow_iff_right hp.one_lt]
  calc
    p ^ finrank (ZMod p) (ModN H p)
    _ = Nat.card (ZMod p) ^ finrank (ZMod p) (ModN H p) := by simp
    _ ≤ p ^ (finrank ℤ H + t) := by grw [← Module.natCard_eq_pow_finrank, natCard_modN, ht, pow_add]

end RankDeduction
