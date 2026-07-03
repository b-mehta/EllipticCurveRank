/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certificate
import ECCompute.ColumnCheck
import ECCompute.Descent
import ECCompute.LambdaCompute
import ECCompute.RankDeduction
import ECCompute.Torsion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The soundness theorem (T9)

This file assembles all the certified pieces of ECCompute into the culminating result
`ECCompute.rank_ge_of_certificate`: **if every referee check on a certificate passes, then the
Mordell–Weil rank of the curve over `ℚ` is at least `ρ − t`.**

## The rank lower bound, stated honestly

The full Mordell–Weil group `E(ℚ)` is not known to be finitely generated inside mathlib
(the Mordell–Weil theorem is not available), so we cannot take `Module.finrank ℤ E(ℚ)` directly.
Following the design's **subgroup trick**, the certificate instead exhibits a *finitely generated*
subgroup `H = ⟨P₁, …, P_ρ⟩` of `E(ℚ)` whose free rank is at least `ρ − t`.  Because the rank of
any subgroup is a lower bound for the rank of the ambient group, this certifies
`rank E(ℚ) ≥ ρ − t` without ever proving `E(ℚ)` finitely generated.

We package this as the predicate `ECCompute.HasRankGE W n`: *there is a finitely generated
`ℤ`-submodule `H` of `W(ℚ)` with `n ≤ finrank ℤ H`.*  This is exactly the certified statement, and
carries no hidden rank definition.

## The chain of certified pieces

Working on the **short integral model** `curve a₂ a₄ a₆` (`y² = x³ + a₂x² + a₄x + a₆`), where the
descent character lives:

1. **T5 / T1.** Each label `(pⱼ, θⱼ)` passing `checkLabel` (and prime) yields a `DescentHyp`
   (`descentHyp_of_checkLabel`), hence the descent character `λ_{pⱼ,θⱼ}` is an additive
   homomorphism `E(ℚ) →+ ZMod 2` (`lambdaHom`).  Bundling the `ρ` columns gives
   `φ : E(ℚ) →+ (Fin ρ → ZMod 2)`.
2. **T4.** The `(i, j)` entry of the certificate matrix `B` equals `λ_{pⱼ,θⱼ}(Pᵢ)`, because the
   kernel-reducible `lambdaCompute` agrees with `lambda` (`lambdaCompute_eq`).  Thus
   `φ(Pᵢ)` is the `i`-th row of `B`.
3. **T3.** `checkInv` passing makes `toMat B` a unit (`checkInv_isUnit`), and an invertible square
   matrix has `𝔽₂`-linearly independent rows (`Matrix.linearIndependent_rows_of_isUnit`).  Hence
   the `φ(Pᵢ)` are linearly independent.
4. **T7.** The torsion witness (`hasRootMod … = false`, giving `t = 0`) shows `E(ℚ)` has no nonzero
   rational `2`-torsion (`no_nonzero_twoTorsion_of_hasRootMod_eq_false`), so `H[2]` is trivial and
   `Nat.card H[2] = 1 = 2⁰`.
5. **T8.** `RankDeduction.rank_ge` combines linear independence with the torsion cardinality to
   conclude `ρ ≤ finrank ℤ H + t`, i.e. `finrank ℤ H ≥ ρ − t`.

## Scope and the general-model transfer (documented gap)

The theorem here is stated on the **short integral model** `curve a₂ a₄ a₆`, which is where the
descent character `lambda` is defined.  A general integral Weierstrass model `toCurveQ a₁ … a₆`
is carried to a short model by completing the square (`ModelIso.nonempty_pointAddEquiv`), and rank
transfers along that isomorphism — the general helper `ECCompute.hasRankGE_of_addEquiv` performs
exactly this transfer along any `AddEquiv` of Mordell–Weil groups.

The one remaining step, deferred to the certificate-elaborator step (T9 part 2 / T10), is that
the short model produced by completing the square has *integer* coefficients so that `lambda`
applies verbatim.  Completing the square `y ↦ y − (a₁x + a₃)/2` produces
`shortModel` with the *rational* coefficients `a₂ + a₁²/4, a₄ + a₁a₃/2, a₆ + a₃²/4`
(`ModelIso.shortModel_a₂` etc.), whereas `lambda`/`DescentHyp`/`checkLabel` are written for the
integer model `curve a₂ a₄ a₆`.  Supplying the integral short model together with the
`AddEquiv` to it (which `hasRankGE_of_addEquiv` consumes) closes the general case; see the
report accompanying this file for the exact interface.
-/

open WeierstrassCurve Module

namespace ECCompute

/-- **The certified rank lower bound.**  `HasRankGE W n` holds when the Mordell–Weil group `W(ℚ)`
contains a finitely generated `ℤ`-submodule of free rank at least `n`.  Since the rank of any
subgroup bounds the rank of the whole group from below, this is exactly the assertion
`rank W(ℚ) ≥ n`, phrased without needing `W(ℚ)` itself to be finitely generated. -/
def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∃ H : Submodule ℤ W.toAffine.Point, Module.Finite ℤ H ∧ n ≤ Module.finrank ℤ H

/-- **Rank lower bounds transfer along Mordell–Weil isomorphisms.**  If the Mordell–Weil groups of
`W₁` and `W₂` are isomorphic as additive groups, then any certified rank lower bound for `W₂` is
also one for `W₁`.  This is the mechanism by which a bound proven on a short model transfers to a
general model related to it by completing the square (`ModelIso.nonempty_pointAddEquiv`). -/
theorem hasRankGE_of_addEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    (e : W₁.toAffine.Point ≃+ W₂.toAffine.Point) {n : ℕ} (h : HasRankGE W₂ n) :
    HasRankGE W₁ n := by
  obtain ⟨H, hfin, hle⟩ := h
  -- View `e` as a `ℤ`-linear equivalence and pull `H` back to `W₁(ℚ)` as `H.map e⁻¹`.
  let el : W₁.toAffine.Point ≃ₗ[ℤ] W₂.toAffine.Point := e.toIntLinearEquiv
  set eq := el.symm.submoduleMap H with heq
  refine ⟨H.map (el.symm : W₂.toAffine.Point →ₗ[ℤ] W₁.toAffine.Point), ?_, ?_⟩
  · -- The image of `H` under the inverse equivalence is isomorphic to `H`, hence f.g.
    have : Module.Finite ℤ H := hfin
    exact Module.Finite.equiv eq
  · rw [← eq.finrank_eq]; exact hle

/-- **The soundness theorem (short integral model).**  Let `c` be a certificate whose curve is the
short integral model `curve c.a₂ c.a₄ c.a₆` (i.e. `a₁ = a₃ = 0`), and suppose every referee check
passes:

* `hpt` — each listed point `pt i` lies on the curve;
* `hlabP`, `hlabC` — each label `lab j = (pⱼ, θⱼ)` is a prime `pⱼ` passing `checkLabel`, so it is a
  legitimate descent column;
* `hB` — the `(i, j)` entry of the character matrix `B` is the computed descent character
  `λ_{pⱼ,θⱼ}(pt i)` (via the kernel-reducible `lambdaCompute`);
* `hinv` — the supplied inverse certifies `B` is invertible over `𝔽₂`;
* `ht`, `htorP`, `htor` — the torsion witness certifies `t = 0`: the monic `2`-division cubic has no
  root modulo the witness prime.

Then the Mordell–Weil rank of `curve c.a₂ c.a₄ c.a₆` over `ℚ` is at least `c.rho − c.t`. -/
theorem rank_ge_of_certificate (c : Certificate)
    (pt : Fin c.rho → ℚ × ℚ) (lab : Fin c.rho → ℕ × ℤ)
    (hpt : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2)
    (hlabP : ∀ j, ((lab j).1).Prime)
    (hlabC : ∀ j, checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 = true)
    (hB : ∀ i j : Fin c.rho,
        F2Invert.toMat c.matB c.rho i j
          = lambdaCompute c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1)
    (hBlen : c.matB.length = c.rho)
    (hMlen : c.matM.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.matB c.matM = true)
    (ht : c.t = 0)
    (htorP : c.torsionPrime ≠ 0)
    (htor : hasRootMod (4 * c.a₂) (16 * c.a₄) (64 * c.a₆) c.torsionPrime = false) :
    HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) := by
  classical
  -- Abbreviations for the curve and its Mordell–Weil group.
  set W : WeierstrassCurve ℚ := curve c.a₂ c.a₄ c.a₆ with hW
  set E : Type := W.toAffine.Point
  -- Each label gives a `Fact` of primality and the descent hypotheses `DescentHyp`.
  haveI factP : ∀ j, Fact ((lab j).1).Prime := fun j => ⟨hlabP j⟩
  have hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) :=
    fun j => descentHyp_of_checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 (hlabC j) (hlabP j)
  -- The bundled descent character `φ : E →+ (Fin ρ → ZMod 2)`.
  set φ : E →+ (Fin c.rho → ZMod 2) :=
    AddMonoidHom.pi (fun j => lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)) with hφ
  -- Handle `ρ = 0` (empty certificate) separately: the bound `0 ≤ finrank` is trivial.
  rcases Nat.eq_zero_or_pos c.rho with hrho0 | hrhopos
  · refine ⟨⊥, inferInstance, ?_⟩
    simp [hrho0]
  -- With `ρ ≥ 1`, pick a label to extract `Δ ≠ 0` (needed to turn `Equation` into `Nonsingular`).
  haveI : Nonempty (Fin c.rho) := ⟨⟨0, hrhopos⟩⟩
  obtain ⟨j₀⟩ := (inferInstance : Nonempty (Fin c.rho))
  have hΔnum : (curve c.a₂ c.a₄ c.a₆).Δ.num ≠ 0 := by
    intro h0
    exact (hyp j₀).discr (by rw [h0]; simp)
  have hΔ : (curve c.a₂ c.a₄ c.a₆).Δ ≠ 0 := fun h => hΔnum (by rw [h]; simp)
  -- Turn each on-curve point into an actual Mordell–Weil group element.
  have hns : ∀ i, W.toAffine.Nonsingular (pt i).1 (pt i).2 := fun i =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  set g : Fin c.rho → E := fun i => .some (pt i).1 (pt i).2 (hns i) with hg
  -- Key computation: `φ(Pᵢ)` is the `i`-th row of the certificate matrix `B`.
  have hrow : (fun i => φ (g i)) = (F2Invert.toMat c.matB c.rho).row := by
    funext i
    ext j
    rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg]
    rw [← lambdaCompute_eq c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j) (pt i).1 (pt i).2 (hns i)]
    exact (hB i j).symm
  -- T3: `B` is a unit, so its rows are `𝔽₂`-linearly independent.
  have hunit : IsUnit (F2Invert.toMat c.matB c.rho) :=
    F2Invert.checkInv_isUnit c.rho c.matB c.matM hBlen hMlen hinv
  have hindep : LinearIndependent (ZMod 2) (fun i => φ (g i)) := by
    rw [hrow]
    exact Matrix.linearIndependent_rows_of_isUnit hunit
  -- The finitely generated subgroup `H = ⟨P₁, …, P_ρ⟩`.
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g) with hH
  haveI hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  -- The points as elements of `H`, and the character restricted to `H`.
  set gH : Fin c.rho → H := fun i => ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩ with hgH
  set φH : H →+ (Fin c.rho → ZMod 2) := φ.comp H.subtype.toAddMonoidHom with hφH
  have hindepH : LinearIndependent (ZMod 2) (fun i => φH (gH i)) := hindep
  -- T7: no nonzero rational `2`-torsion, so `H[2]` is trivial.
  have htorsion : Submodule.torsionBy ℤ H 2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_torsionBy_iff] at hx
    rw [Submodule.mem_bot]
    -- `(2 : ℤ) • x = 0` in `H` means the underlying point is `2`-torsion in `E`.
    have hxE : (x : E) + (x : E) = 0 := by
      have : ((2 : ℤ) • x : H) = 0 := hx
      have h2 : (2 : ℤ) • (x : E) = 0 := by
        rw [← Submodule.coe_smul, this, Submodule.coe_zero]
      rwa [two_zsmul] at h2
    have hx0 : (x : E) = 0 :=
      no_nonzero_twoTorsion_of_hasRootMod_eq_false 0 c.a₂ 0 c.a₄ c.a₆ htorP W
        (by simp [hW, curve]) (by simp [hW, curve]) (by simp [hW, curve])
        (by simp [hW, curve]) (by simp [hW, curve])
        (by rw [show (0 : ℤ) ^ 2 + 4 * c.a₂ = 4 * c.a₂ by ring,
            show 8 * (2 * c.a₄ + 0 * 0) = 16 * c.a₄ by ring,
            show 16 * ((0 : ℤ) ^ 2 + 4 * c.a₆) = 64 * c.a₆ by ring]; exact htor)
        (x : E) hxE
    exact Subtype.ext hx0
  have htcard : Nat.card (Submodule.torsionBy ℤ H 2) = 2 ^ 0 := by
    rw [htorsion, pow_zero]; exact Nat.card_unique
  -- T8: assemble the deduction.
  have hbound : c.rho ≤ Module.finrank ℤ H + 0 :=
    RankDeduction.rank_ge (H := H) gH φH hindepH htcard
  refine ⟨H, hHfin, ?_⟩
  rw [ht, Nat.sub_zero]
  simpa using hbound

end ECCompute
