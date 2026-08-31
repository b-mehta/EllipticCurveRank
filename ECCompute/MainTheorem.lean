/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Certificate
public import ECCompute.Theory.RankDeduction
public import ECCompute.Theory.Model
import ECCompute.Soundness.Labels
import ECCompute.Soundness.Points
import ECCompute.Soundness.Primes
import ECCompute.Soundness.DescentMatrix
import ECCompute.Soundness.Torsion
import ECCompute.Theory.Descent.Additivity
import ECCompute.Soundness.LambdaCompute
import ECCompute.ForMathlib.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The main theory: a rank lower bound from a certificate

This file assembles the certified pieces into the statement that a passing certificate forces a
lower bound on the Mordell-Weil rank of an elliptic curve over `ℚ`, and delivers that bound for a
*general* integral Weierstrass model.

## Main results

* `hasRankGE_of_certificate`: the bound for an arbitrary curve `W` whose coefficients are the
  integers `a₁ … a₆`, obtained by transporting the short-model bound back along the
  complete-the-square and scaling changes of variables.
-/

namespace ECCompute

open WeierstrassCurve Module

/-- `HasRankGE W n` holds when the Mordell-Weil group `W(ℚ)` contains a finitely generated
`ℤ`-submodule of free rank at least `n`, which is exactly `rank W(ℚ) ≥ n`. -/
@[expose]
public def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∃ H : Submodule ℤ W.toAffine.Point, Module.Finite ℤ H ∧ n ≤ finrank ℤ H

/-- If the Mordell-Weil groups of `W₁` and `W₂` are isomorphic as additive groups, then any
certified rank lower bound for `W₂` is also one for `W₁`. -/
theorem hasRankGE_of_addEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    (e : W₁.toAffine.Point ≃+ W₂.toAffine.Point) {n : ℕ} (h : HasRankGE W₂ n) :
    HasRankGE W₁ n := by
  obtain ⟨H, hfin, hle⟩ := h
  -- View `e` as a `ℤ`-linear equivalence and pull `H` back to `W₁(ℚ)` as `H.map e⁻¹`.
  let el : W₁.toAffine.Point ≃ₗ[ℤ] W₂.toAffine.Point := e.toIntLinearEquiv
  set emap := el.symm.submoduleMap H
  refine ⟨H.map (el.symm : W₂.toAffine.Point →ₗ[ℤ] W₁.toAffine.Point), ?_, ?_⟩
  · exact Module.Finite.equiv emap
  · rwa [← emap.finrank_eq]

variable {a₂ a₄ a₆ : ℤ}
variable {c : Certificate} {pt : Fin c.ρ → ℚ × ℚ} {ls : Fin c.ρ → ℕ × ℤ}

/-- The `2`-torsion of the span `H` of the certified points embeds into the `2`-torsion of the whole
curve, so its cardinality is bounded by `|E(ℚ)[2]|`. -/
theorem card_torsionBy_le (H : Submodule ℤ (curveQ a₂ a₄ a₆).toAffine.Point) :
    Nat.card (Submodule.torsionBy ℤ H 2) ≤ (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard := by
  have hmap (x : Submodule.torsionBy ℤ H 2) :
      (x : (curveQ a₂ a₄ a₆).toAffine.Point) ∈ (curveQ a₂ a₄ a₆).twoTorsionPoints := by
    rw [mem_twoTorsionPoints, ← two_zsmul, ← Submodule.coe_smul, Submodule.smul_coe_torsionBy,
      Submodule.coe_zero]
  refine Nat.card_le_card_of_injective (fun x ↦ ⟨x, hmap x⟩) fun a b hab ↦ ?_
  grind

/-- The rank bound for a general integral model: given `W = ⟨a₁, …, a₆⟩` (`hW`), proofs that its
short-model coefficients `a₁²+4a₂, 16a₄+8a₁a₃, 64a₆+16a₃²` are the certificate's `c.a₂, c.a₄, c.a₆`
(`h₂ h₄ h₆`), and a certificate satisfying `Certificate.Valid` (`hc`), the rank of `W` is at least
`c.ρ - c.t`. -/
public theorem hasRankGE_of_certificate {a₁ a₂ a₃ a₄ a₆ : ℤ} (c : Certificate)
    (W : WeierstrassCurve ℚ)
    (hW : W = ⟨a₁, a₂, a₃, a₄, a₆⟩) (h₂ : a₁ ^ 2 + 4 * a₂ = c.a₂)
    (h₄ : 16 * a₄ + 8 * a₁ * a₃ = c.a₄) (h₆ : 64 * a₆ + 16 * a₃ ^ 2 = c.a₆)
    (hc : c.Valid) :
    HasRankGE W (c.ρ - c.t) := by
  obtain ⟨hlenP, hlenL, hlenB, hlenM, hlenQ, hpt, hlsP, hlsC, hB, hinv, htors⟩ := hc
  subst hW
  suffices this : HasRankGE (curveQ c.a₂ c.a₄ c.a₆) (c.ρ - c.t) by
    set W : WeierstrassCurve ℚ := ⟨a₁, a₂, a₃, a₄, a₆⟩
    -- Complete the square (`toCharNeTwoNF`) and scale by `2` (the change `⟨1/2, 0, 0, 0⟩`), as a
    -- single variable change `C`, to land on the certificate's integral short model.
    set C : VariableChange ℚ := ⟨(Units.mk0 2 two_ne_zero)⁻¹, 0, 0, 0⟩ * W.toCharNeTwoNF with hC
    have hsm : C • W = curveQ c.a₂ c.a₄ c.a₆ := by
      rw [hC, mul_smul, ← h₂, ← h₄, ← h₆]
      ext <;>
      simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
        variableChange_a₆, curve] <;>
      grind
    exact hasRankGE_of_addEquiv C.pointAddEquiv (hsm ▸ this)
  clear h₂ h₄ h₆ a₁ a₂ a₃ a₄ a₆
  rw [checkPoints_iff] at hpt
  set pt : Fin c.ρ → ℚ × ℚ := fun i ↦ c.points[i]
  set ls : Fin c.ρ → ℕ × ℤ := fun j ↦ c.labels[j]
  replace hlsP (j : Fin c.ρ) : (ls j).1.Prime := checkPrimes_true hlsP _ (List.getElem_mem _)
  replace hlsC (j : Fin c.ρ) : checkLabel c.a₂ c.a₄ c.a₆ (ls j).1 (ls j).2 :=
    checkLabels_true hlsC _ (List.getElem_mem _)
  replace hlsC (j) : DescentHyp c.a₂ c.a₄ c.a₆ (ls j).1 (ls j).2 :=
    descentHyp_of_checkLabel (hlsC j) (hlsP j)
  replace hpt (i : Fin c.ρ) : (curveQ c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2 :=
    hpt _ (List.getElem_mem _)
  have hBmat : ∀ i j, F2Invert.toMat c.B c.ρ i j =
      if lambdaK c.a₂ c.a₄ (ls j).1 (qrMask (ls j).1) ((ls j).2 % (ls j).1).toNat
          (pt i).1.num.toNat (-(pt i).1.num).toNat (pt i).1.den then 1 else 0 :=
    checkB_true hlenB hlenP hlenL hlenQ hB
  set E : Type := (curveQ c.a₂ c.a₄ c.a₆).toAffine.Point
  set φ : E →+ (Fin c.ρ → ZMod 2) := AddMonoidHom.pi (fun j ↦ lambdaHom (hlsC j)) with hφ
  rcases Nat.eq_zero_or_pos c.ρ with hρ0 | hρpos
  · exact ⟨⊥, inferInstance, by simp [hρ0]⟩
  have hΔ : (curveQ c.a₂ c.a₄ c.a₆).Δ ≠ 0 := fun hΔ0 ↦ (hlsC ⟨0, hρpos⟩).discr (by simp [hΔ0])
  have hns (i) : (curveQ c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2 :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  let (eq := hg) g (i : Fin c.ρ) : E := .some (pt i).1 (pt i).2 (hns i)
  -- The `g i` are the rows of the invertible `B`, so `φ` maps them to an independent family.
  have hindep : LinearIndependent (ZMod 2) (fun i ↦ φ (g i)) := by
    have hrow : (fun i ↦ φ (g i)) = (F2Invert.toMat c.B c.ρ).row := by
      ext i j
      rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg,
        ← lambdaK_eq (hlsC j) (hns i) (intResNat_cast (hlsC j).prime.ne_zero)
          (Int.toNat_sub_toNat_neg (pt i).1.num).symm rfl]
      simp [hBmat]
    rw [hrow]
    exact Matrix.linearIndependent_rows_of_isUnit (F2Invert.checkInv_isUnit hlenB hlenM hinv)
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  have hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  refine ⟨H, hHfin, ?_⟩
  simpa using RankDeduction.rank_ge_le (H := H) Nat.prime_two
    (fun i ↦ ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩) (φ.comp H.subtype.toAddMonoidHom)
    hindep ((card_torsionBy_le H).trans htors)

end ECCompute
