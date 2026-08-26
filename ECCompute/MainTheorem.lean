/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certificate
import ECCompute.Soundness.Labels
import ECCompute.Soundness.Points
import ECCompute.Soundness.Primes
import ECCompute.Soundness.DescentMatrix
import ECCompute.Soundness.Torsion
import ECCompute.Theory.Descent
import ECCompute.Soundness.LambdaCompute
import ECCompute.Theory.RankDeduction
import ECCompute.Theory.IntegralScaling
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The main theory: a rank lower bound from a certificate

This file assembles the certified pieces into the statement that a passing certificate forces a
lower bound on the Mordell-Weil rank of an elliptic curve over `ℚ`, and delivers that bound for a
*general* integral Weierstrass model.

## Main results

* `rank_ge_of_certificate`: the bound on the short integral model `curve c.a₂ c.a₄ c.a₆`, where the
  descent character lives.
* `hasRankGE_of_certificate`: the bound for an arbitrary curve `W` whose coefficients are the
  integers `a₁ … a₆`, obtained by transporting the short-model bound along
  `IntegralScaling.generalToShortEquiv`.
-/

namespace ECCompute

open WeierstrassCurve Module CompleteSquare IntegralScaling

/-- `HasRankGE W n` holds when the Mordell-Weil group `W(ℚ)` contains a finitely generated
`ℤ`-submodule of free rank at least `n`, which is exactly `rank W(ℚ) ≥ n`. -/
def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
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
  · -- The image of `H` under the inverse equivalence is isomorphic to `H`, hence f.g.
    exact Module.Finite.equiv (M := H) emap
  · rwa [← emap.finrank_eq]

/-- A descent hypothesis for `curve a₂ a₄ a₆` witnesses that its discriminant is nonzero. -/
private theorem discr_ne_zero_of_descentHyp {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}
    (h : DescentHyp a₂ a₄ a₆ p θ) : (curve a₂ a₄ a₆).Δ ≠ 0 :=
  fun hΔ ↦ h.discr (by simp [hΔ])

/-- The descent character `φ` sends the certified points `g` to the rows of the character matrix
`B`, so linear independence of those rows over `𝔽₂` transfers to the points. -/
private theorem linearIndependent_descent {c : Certificate} {lab : Fin c.rho → ℕ × ℤ}
    (hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1))
    {pt : Fin c.rho → ℚ × ℚ}
    (hns : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2)
    (hB : ∀ i j, F2Invert.toMat c.B c.rho i j
        = if lambdaComputeBoolNatMask c.a₂ c.a₄ (lab j).1 (qrMask (lab j).1)
            ((lab j).2 % (lab j).1).toNat
            (pt i).1.num.toNat (-(pt i).1.num).toNat (pt i).1.den then 1 else 0)
    (hBlen : c.B.length = c.rho) (hMlen : c.M.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.B c.M)
    {φ : (curve c.a₂ c.a₄ c.a₆).toAffine.Point →+ (Fin c.rho → ZMod 2)}
    (hφ : φ = AddMonoidHom.pi (fun j ↦ lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)))
    {g : Fin c.rho → (curve c.a₂ c.a₄ c.a₆).toAffine.Point}
    (hg : g = fun i ↦ .some (pt i).1 (pt i).2 (hns i)) :
    LinearIndependent (ZMod 2) (fun i ↦ φ (g i)) := by
  have hrow : (fun i ↦ φ (g i)) = (F2Invert.toMat c.B c.rho).row := by
    ext i j
    have : Fact ((lab j).1).Prime := ⟨(hyp j).prime⟩
    rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg,
      ← lambdaComputeBoolNatMask_eq (hyp j) (hns i)
        (intResNat_cast (hyp j).prime.ne_zero)
        (Int.toNat_sub_toNat_neg (pt i).1.num).symm rfl]
    simp [hB]
  rw [hrow]
  exact Matrix.linearIndependent_rows_of_isUnit (F2Invert.checkInv_isUnit hBlen hMlen hinv)

/-- The `2`-torsion of the span `H` of the certified points embeds into the `2`-torsion of the whole
curve, so its cardinality is bounded by `|E(ℚ)[2]|`. -/
private theorem card_torsionBy_le {a₂ a₄ a₆ : ℤ}
    (H : Submodule ℤ (curve a₂ a₄ a₆).toAffine.Point) :
    Nat.card (Submodule.torsionBy ℤ H 2) ≤ (curve a₂ a₄ a₆).twoTorsionPoints.ncard := by
  have hmap (x : Submodule.torsionBy ℤ H 2) :
      (x : (curve a₂ a₄ a₆).toAffine.Point) ∈ (curve a₂ a₄ a₆).twoTorsionPoints := by
    rw [mem_twoTorsionPoints, ← two_zsmul, ← Submodule.coe_smul, Submodule.smul_coe_torsionBy,
      Submodule.coe_zero]
  refine Nat.card_le_card_of_injective (fun x ↦ ⟨((x : H) : _), hmap x⟩) fun a b hab ↦ ?_
  grind

/-- Soundness on the short integral model `curve c.a₂ c.a₄ c.a₆` (`a₁ = a₃ = 0`): when the
certificate's points, labels, character matrix `B`, its `𝔽₂`-inverse, and its torsion witness all
pass their checks, the rank is at least `c.rho - c.t`. -/
theorem rank_ge_of_certificate (c : Certificate)
    {pt : Fin c.rho → ℚ × ℚ} {lab : Fin c.rho → ℕ × ℤ}
    (hpt : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2)
    (hlabP : ∀ j, ((lab j).1).Prime)
    (hlabC : ∀ j, checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2)
    (hB : ∀ i j, F2Invert.toMat c.B c.rho i j =
      if lambdaComputeBoolNatMask c.a₂ c.a₄ (lab j).1 (qrMask (lab j).1)
          ((lab j).2 % (lab j).1).toNat
          (pt i).1.num.toNat (-(pt i).1.num).toNat (pt i).1.den then 1 else 0)
    (hBlen : c.B.length = c.rho)
    (hMlen : c.M.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.B c.M)
    (htors : (curve c.a₂ c.a₄ c.a₆).twoTorsionPoints.ncard ≤ 2 ^ c.t) :
    HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) := by
  classical
  set E : Type := (curve c.a₂ c.a₄ c.a₆).toAffine.Point
  have hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) :=
    fun j ↦ descentHyp_of_checkLabel (hlabC j) (hlabP j)
  set φ : E →+ (Fin c.rho → ZMod 2) :=
    AddMonoidHom.pi (fun j ↦ lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)) with hφ
  rcases Nat.eq_zero_or_pos c.rho with hrho0 | hrhopos
  · exact ⟨⊥, inferInstance, by simp [hrho0]⟩
  obtain ⟨j₀⟩ : Nonempty (Fin c.rho) := ⟨⟨0, hrhopos⟩⟩
  have hΔ : (curve c.a₂ c.a₄ c.a₆).Δ ≠ 0 := discr_ne_zero_of_descentHyp (hyp j₀)
  have hns (i) : (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2 :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  let (eq := hg) g (i : Fin c.rho) : E := .some (pt i).1 (pt i).2 (hns i)
  -- The `g i` are the rows of the invertible `B`, so `φ` maps them to an independent family.
  have hindep : LinearIndependent (ZMod 2) (fun i ↦ φ (g i)) :=
    linearIndependent_descent hyp hns hB hBlen hMlen hinv hφ hg
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  have hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  have htorH : Nat.card (Submodule.torsionBy ℤ H 2) ≤ 2 ^ c.t :=
    (card_torsionBy_le H).trans htors
  have hbound : c.rho ≤ finrank ℤ H + c.t := RankDeduction.rank_ge_le
    (fun i ↦ ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩)
    (φ.comp H.subtype.toAddMonoidHom) hindep htorH
  exact ⟨H, hHfin, Nat.sub_le_iff_le_add.mpr hbound⟩

/-- The rank bound for a general integral model: given `W = ⟨a₁, …, a₆⟩` (`hW`), a proof that the
short model of these coefficients is the certificate's curve (`hmodel`), and a certificate
satisfying `Certificate.Valid` (`hc`), the rank of `W` is at least `c.rho - c.t`. -/
theorem hasRankGE_of_certificate {a₁ a₂ a₃ a₄ a₆ : ℤ} (c : Certificate) (W : WeierstrassCurve ℚ)
    (hW : W = ⟨a₁, a₂, a₃, a₄, a₆⟩) (hmodel : intShortModel a₁ a₂ a₃ a₄ a₆ = curve c.a₂ c.a₄ c.a₆)
    (hc : c.Valid) :
    HasRankGE W (c.rho - c.t) := by
  obtain ⟨hlenP, hlenL, hlenB, hlenM, hlenQ, hpt, hlabP, hlabC, hB, hinv, htors⟩ := hc
  rw [hW]
  rw [checkPoints_iff] at hpt
  have hlabP' (j : Fin c.rho) : c.labels[j].1.Prime :=
    checkPrimes_true hlabP _ (List.getElem_mem _)
  have hlabC' (j : Fin c.rho) : checkLabel c.a₂ c.a₄ c.a₆ c.labels[j].1 c.labels[j].2 :=
    checkLabels_true hlabC _ (List.getElem_mem _)
  have key : HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) :=
    rank_ge_of_certificate c (fun i ↦ hpt _ (List.getElem_mem _)) hlabP' hlabC'
      (checkB_true hlenB hlenP hlenL hlenQ hB) hlenB hlenM hinv htors
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
