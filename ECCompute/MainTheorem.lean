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

/-- Two Weierstrass curves over `ℚ` are equal when their five coefficients agree, each certified
by a kernel-reducible `BEq` check. -/
theorem _root_.WeierstrassCurve.ext_of_beq {W W' : WeierstrassCurve ℚ}
    (h₁ : (W.a₁ == W'.a₁) = true) (h₂ : (W.a₂ == W'.a₂) = true) (h₃ : (W.a₃ == W'.a₃) = true)
    (h₄ : (W.a₄ == W'.a₄) = true) (h₆ : (W.a₆ == W'.a₆) = true) : W = W' := by
  cases W; cases W'
  simp only [WeierstrassCurve.mk.injEq]
  exact ⟨eq_of_beq h₁, eq_of_beq h₂, eq_of_beq h₃, eq_of_beq h₄, eq_of_beq h₆⟩

/-- `HasRankGE W n` holds when the Mordell-Weil group `W(ℚ)` contains a finitely generated
`ℤ`-submodule of free rank at least `n`, which is exactly `rank W(ℚ) ≥ n`. -/
def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∃ H : Submodule ℤ W.toAffine.Point, Module.Finite ℤ H ∧ n ≤ Module.finrank ℤ H

/-- If the Mordell-Weil groups of `W₁` and `W₂` are isomorphic as additive groups, then any
certified rank lower bound for `W₂` is also one for `W₁`. -/
theorem hasRankGE_of_addEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    (e : W₁.toAffine.Point ≃+ W₂.toAffine.Point) {n : ℕ} (h : HasRankGE W₂ n) :
    HasRankGE W₁ n := by
  obtain ⟨H, hfin, hle⟩ := h
  -- View `e` as a `ℤ`-linear equivalence and pull `H` back to `W₁(ℚ)` as `H.map e⁻¹`.
  let el : W₁.toAffine.Point ≃ₗ[ℤ] W₂.toAffine.Point := e.toIntLinearEquiv
  set eq := el.symm.submoduleMap H
  refine ⟨H.map (el.symm : W₂.toAffine.Point →ₗ[ℤ] W₁.toAffine.Point), ?_, ?_⟩
  · -- The image of `H` under the inverse equivalence is isomorphic to `H`, hence f.g.
    exact Module.Finite.equiv (M := H) eq
  · rwa [← eq.finrank_eq]

/-- A descent hypothesis for `curve a₂ a₄ a₆` witnesses that its discriminant is nonzero. -/
private theorem discr_ne_zero_of_descentHyp {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}
    (h : DescentHyp a₂ a₄ a₆ p θ) : (curve a₂ a₄ a₆).Δ ≠ 0 := by
  intro hΔ
  exact h.discr (by simp [hΔ])

/-- The descent character `φ` sends the certified points `g` to the rows of the character matrix
`B`, so linear independence of those rows over `𝔽₂` transfers to the points. -/
private theorem linearIndependent_descent {c : Certificate} {lab : Fin c.rho → ℕ × ℤ}
    (hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1))
    (pt : Fin c.rho → ℚ × ℚ)
    (hns : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2)
    (hB : ∀ i j, F2Invert.toMat c.B c.rho i j
        = lambdaCompute c.a₂ c.a₄ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1)
    (hBlen : c.B.length = c.rho) (hMlen : c.M.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.B c.M = true)
    (φ : (curve c.a₂ c.a₄ c.a₆).toAffine.Point →+ (Fin c.rho → ZMod 2))
    (hφ : φ = AddMonoidHom.pi (fun j => lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)))
    (g : Fin c.rho → (curve c.a₂ c.a₄ c.a₆).toAffine.Point)
    (hg : g = fun i => .some (pt i).1 (pt i).2 (hns i)) :
    LinearIndependent (ZMod 2) (fun i => φ (g i)) := by
  have hrow : (fun i => φ (g i)) = (F2Invert.toMat c.B c.rho).row := by
    funext i
    ext j
    rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg,
      ← lambdaCompute_eq c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j) (pt i).1 (pt i).2 (hns i)]
    exact (hB i j).symm
  rw [hrow]
  exact Matrix.linearIndependent_rows_of_isUnit
    (F2Invert.checkInv_isUnit hBlen hMlen hinv)

/-- The `2`-torsion of the span `H` of the certified points embeds into the `2`-torsion of the whole
curve, so its cardinality is bounded by `|E(ℚ)[2]|`. -/
private theorem card_torsionBy_le (a₂ a₄ a₆ : ℤ)
    (H : Submodule ℤ (curve a₂ a₄ a₆).toAffine.Point) :
    Nat.card (Submodule.torsionBy ℤ H 2) ≤
      Nat.card {P : (curve a₂ a₄ a₆).toAffine.Point // P + P = 0} := by
  have hmap : ∀ x : Submodule.torsionBy ℤ H 2,
      ((x : H) : (curve a₂ a₄ a₆).toAffine.Point) + ((x : H) : _) = 0 := by
    intro x
    have hx : (2 : ℤ) • (x : H) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rw [← two_zsmul, ← Submodule.coe_smul, hx, Submodule.coe_zero]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : H) : _), hmap x⟩) fun a b hab => ?_
  have h := congrArg Subtype.val hab
  exact Subtype.coe_injective (Subtype.coe_injective h)

/-- Soundness on the short integral model `curve c.a₂ c.a₄ c.a₆` (`a₁ = a₃ = 0`). When a
certificate's points, labels, character matrix `B`, its claimed `𝔽₂`-inverse and its torsion
witness all pass their checks (the hypotheses `hpt` through `htors`), the rank is at least
`c.rho - c.t`. The proof reads `B` as `c.rho` descent images that invertibility makes
`𝔽₂`-independent, then feeds them to `RankDeduction.rank_ge_le`. -/
theorem rank_ge_of_certificate (c : Certificate)
    (pt : Fin c.rho → ℚ × ℚ) (lab : Fin c.rho → ℕ × ℤ)
    (hpt : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2)
    (hlabP : ∀ j, ((lab j).1).Prime)
    (hlabC : ∀ j, checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 = true)
    (hB : ∀ i j : Fin c.rho,
        F2Invert.toMat c.B c.rho i j
          = lambdaCompute c.a₂ c.a₄ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1)
    (hBlen : c.B.length = c.rho)
    (hMlen : c.M.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.B c.M = true)
    (htors : Nat.card {P : (curve c.a₂ c.a₄ c.a₆).toAffine.Point // P + P = 0} ≤ 2 ^ c.t) :
    HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) := by
  classical
  set E : Type := (curve c.a₂ c.a₄ c.a₆).toAffine.Point
  have hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) :=
    fun j => descentHyp_of_checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 (hlabC j) (hlabP j)
  set φ : E →+ (Fin c.rho → ZMod 2) :=
    AddMonoidHom.pi (fun j => lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)) with hφ
  rcases Nat.eq_zero_or_pos c.rho with hrho0 | hrhopos
  · exact ⟨⊥, inferInstance, by simp [hrho0]⟩
  obtain ⟨j₀⟩ : Nonempty (Fin c.rho) := ⟨⟨0, hrhopos⟩⟩
  have hΔ : (curve c.a₂ c.a₄ c.a₆).Δ ≠ 0 := discr_ne_zero_of_descentHyp (hyp j₀)
  have hns : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2 := fun i =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  set g : Fin c.rho → E := fun i => .some (pt i).1 (pt i).2 (hns i) with hg
  -- The `g i` are the rows of the invertible `B`, so `φ` maps them to an independent family.
  have hindep : LinearIndependent (ZMod 2) (fun i => φ (g i)) :=
    linearIndependent_descent hyp pt hns hB hBlen hMlen hinv φ hφ g hg
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  have hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  set gH : Fin c.rho → H := fun i => ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩
  set φH : H →+ (Fin c.rho → ZMod 2) := φ.comp H.subtype.toAddMonoidHom
  have htorH : Nat.card (Submodule.torsionBy ℤ H 2) ≤ 2 ^ c.t :=
    (card_torsionBy_le c.a₂ c.a₄ c.a₆ H).trans htors
  have hbound : c.rho ≤ Module.finrank ℤ H + c.t := RankDeduction.rank_ge_le gH φH hindep htorH
  exact ⟨H, hHfin, Nat.sub_le_iff_le_add.mpr hbound⟩

/-- The same bound for a general integral model. Given `W = ⟨a₁, …, a₆⟩` (`hW`) whose short-model
change of variables is the certificate's curve (`hmodel`), transporting `rank_ge_of_certificate`
along `generalToShortEquiv` gives `rank W ≥ c.rho - c.t`. -/
theorem hasRankGE_of_certificate (a₁ a₂ a₃ a₄ a₆ : ℤ) (c : Certificate)
    (W : WeierstrassCurve ℚ)
    (hW : W = ⟨a₁, a₂, a₃, a₄, a₆⟩)
    (hmodel : intShortModel a₁ a₂ a₃ a₄ a₆ = curve c.a₂ c.a₄ c.a₆)
    (hlenP : c.points.length = c.rho)
    (hlenL : c.labels.length = c.rho)
    (hlenB : c.B.length = c.rho)
    (hlenM : c.M.length = c.rho)
    (hlenQ : c.qrMasks.length = c.rho)
    (hpt : checkPoints 0 c.a₂ 0 c.a₄ c.a₆ c.points = true)
    (hlabP : checkPrimes c.labels = true)
    (hlabC : checkLabels c.a₂ c.a₄ c.a₆ c.labels = true)
    (hB : checkB c.a₂ c.a₄ c.labels c.qrMasks c.B c.points = true)
    (hinv : F2Invert.checkInv c.rho c.B c.M = true)
    (htors : Nat.card {P : (curve c.a₂ c.a₄ c.a₆).toAffine.Point // P + P = 0} ≤ 2 ^ c.t) :
    HasRankGE W (c.rho - c.t) := by
  -- Reduce to the integral model `⟨a₁, …, a₆⟩`, which `W` equals by `hW`.
  rw [hW]
  -- The point/label families the soundness theorem consumes are read from the certificate's lists
  -- by index. Every kernel-checked hypothesis above is `List`-based; the families here appear
  -- only in the (non-computational) proof.
  have hmemP : ∀ i : Fin c.rho, c.points[i] ∈ c.points := fun i => List.getElem_mem _
  have hmemL : ∀ j : Fin c.rho, c.labels[j] ∈ c.labels := fun j => List.getElem_mem _
  have hcurve : curve c.a₂ c.a₄ c.a₆ = (⟨0, c.a₂, 0, c.a₄, c.a₆⟩ : WeierstrassCurve ℚ) := by
    simp only [curve]
  rw [checkPoints_iff] at hpt
  have hpt' : ∀ i : Fin c.rho, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation
      c.points[i].1 c.points[i].2 := by
    intro i
    rw [hcurve]
    exact hpt _ (hmemP i)
  have hlabP' : ∀ j : Fin c.rho, (c.labels[j].1).Prime :=
    fun j => checkPrimes_true hlabP _ (hmemL j)
  have hlabC' : ∀ j : Fin c.rho, checkLabel c.a₂ c.a₄ c.a₆
      c.labels[j].1 c.labels[j].2 = true :=
    fun j => checkLabels_true hlabC _ (hmemL j)
  have key : HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) :=
    rank_ge_of_certificate c (fun i => c.points[i]) (fun j => c.labels[j])
      hpt' hlabP' hlabC'
      (checkB_true hlenB hlenP hlenL hlenQ hlabP' hB) hlenB hlenM hinv htors
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
