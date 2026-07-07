/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify.Certificate
import ECCompute.Check.ColumnCheck
import ECCompute.Check.Points
import ECCompute.Check.Primes
import ECCompute.Check.CheckMatrix
import ECCompute.Check.Torsion
import ECCompute.Theory.Descent
import ECCompute.Theory.LambdaCompute
import ECCompute.Theory.RankDeduction
import ECCompute.Theory.ModelChange
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.NormNum.Prime

/-!
# The main theory: a rank lower bound from a certificate

This file assembles the certified pieces into the statement that a passing certificate forces a
lower bound on the Mordell-Weil rank of an elliptic curve over `ℚ`, and delivers that bound for a
*general* integral Weierstrass model.

## Main results

* `rank_ge_of_certificate`: the bound on the short integral model `curve c.a₂ c.a₄ c.a₆`, where the
  descent character lives.
* `hasRankGE_of_certificate`: the front door for a general model `toCurveQ a₁ … a₆`, obtained by
  transporting the short-model bound along `ModelChange.generalToShortEquiv`.
-/

namespace ECCompute

open WeierstrassCurve Module ModelIso ModelChange

/-- Two Weierstrass curves over `ℚ` are equal when their five coefficients agree, each certified by a
kernel-reducible `BEq` check. -/
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
  set eq := el.symm.submoduleMap H with heq
  refine ⟨H.map (el.symm : W₂.toAffine.Point →ₗ[ℤ] W₁.toAffine.Point), ?_, ?_⟩
  · -- The image of `H` under the inverse equivalence is isomorphic to `H`, hence f.g.
    have : Module.Finite ℤ H := hfin
    exact Module.Finite.equiv eq
  · rw [← eq.finrank_eq]
    exact hle

/-- A descent hypothesis for `curve a₂ a₄ a₆` witnesses that its discriminant is nonzero. -/
private theorem discr_ne_zero_of_descentHyp {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}
    (h : DescentHyp a₂ a₄ a₆ p θ) : (curve a₂ a₄ a₆).Δ ≠ 0 := by
  intro hΔ
  exact h.discr (by rw [hΔ]; simp)

/-- The descent character `φ` sends the certified points `g` to the rows of the character matrix
`B`, so linear independence of those rows over `𝔽₂` transfers to the points. -/
private theorem linearIndependent_descent {c : Certificate} {lab : Fin c.rho → ℕ × ℤ}
    (hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1))
    (pt : Fin c.rho → ℚ × ℚ)
    (hns : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2)
    (hB : ∀ i j, F2Invert.toMat c.matB c.rho i j
        = lambdaCompute c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) (pt i).1)
    (hBlen : c.matB.length = c.rho) (hMlen : c.matM.length = c.rho)
    (hinv : F2Invert.checkInv c.rho c.matB c.matM = true)
    (φ : (curve c.a₂ c.a₄ c.a₆).toAffine.Point →+ (Fin c.rho → ZMod 2))
    (hφ : φ = AddMonoidHom.pi (fun j => lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)))
    (g : Fin c.rho → (curve c.a₂ c.a₄ c.a₆).toAffine.Point)
    (hg : g = fun i => .some (pt i).1 (pt i).2 (hns i)) :
    LinearIndependent (ZMod 2) (fun i => φ (g i)) := by
  have hrow : (fun i => φ (g i)) = (F2Invert.toMat c.matB c.rho).row := by
    funext i
    ext j
    rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg,
      ← lambdaCompute_eq c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j) (pt i).1 (pt i).2 (hns i)]
    exact (hB i j).symm
  rw [hrow]
  exact Matrix.linearIndependent_rows_of_isUnit
    (F2Invert.checkInv_isUnit c.rho c.matB c.matM hBlen hMlen hinv)

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
    have h2 : (2 : ℤ) • ((x : H) : (curve a₂ a₄ a₆).toAffine.Point) = 0 := by
      rw [← Submodule.coe_smul, hx, Submodule.coe_zero]
    rwa [two_zsmul] at h2
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : H) : _), hmap x⟩) ?_
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.coe_injective (Subtype.coe_injective h)

/-- The soundness theorem on the short integral model.  Let `c` be a certificate whose curve is the
short integral model `curve c.a₂ c.a₄ c.a₆` (i.e. `a₁ = a₃ = 0`), and suppose every referee check
passes:

* `hpt`: each listed point `pt i` lies on the curve;
* `hlabP`, `hlabC`: each label `lab j = (pⱼ, θⱼ)` is a prime `pⱼ` passing `checkLabel`, so it is a
  legitimate descent column;
* `hB`: the `(i, j)` entry of the character matrix `B` is the computed descent character
  `λ_{pⱼ,θⱼ}(pt i)` (via the kernel-reducible `lambdaCompute`);
* `hinv`: the supplied inverse certifies `B` is invertible over `𝔽₂`;
* `htors`: the torsion witness bounds the rational `2`-torsion of the curve, `|E(ℚ)[2]| ≤ 2^t`.

Then the Mordell-Weil rank of `curve c.a₂ c.a₄ c.a₆` over `ℚ` is at least `c.rho - c.t`. -/
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
    (htors : Nat.card {P : (curve c.a₂ c.a₄ c.a₆).toAffine.Point // P + P = 0} ≤ 2 ^ c.t) :
    HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) := by
  classical
  set E : Type := (curve c.a₂ c.a₄ c.a₆).toAffine.Point
  -- Each label gives the descent hypotheses `DescentHyp`.
  have hyp : ∀ j, DescentHyp c.a₂ c.a₄ c.a₆ (lab j).1 ((lab j).2 : ZMod (lab j).1) :=
    fun j => descentHyp_of_checkLabel c.a₂ c.a₄ c.a₆ (lab j).1 (lab j).2 (hlabC j) (hlabP j)
  -- The bundled descent character `φ : E →+ (Fin ρ → ZMod 2)`.
  set φ : E →+ (Fin c.rho → ZMod 2) :=
    AddMonoidHom.pi (fun j => lambdaHom c.a₂ c.a₄ c.a₆ (lab j).1 (hyp j)) with hφ
  -- Handle `ρ = 0` (empty certificate) separately: the bound `0 ≤ finrank` is trivial.
  rcases Nat.eq_zero_or_pos c.rho with hrho0 | hrhopos
  · exact ⟨⊥, inferInstance, by simp [hrho0]⟩
  -- With `ρ ≥ 1`, pick a label to extract `Δ ≠ 0` (turns `Equation` into `Nonsingular`).
  obtain ⟨j₀⟩ : Nonempty (Fin c.rho) := ⟨⟨0, hrhopos⟩⟩
  have hΔ : (curve c.a₂ c.a₄ c.a₆).Δ ≠ 0 := discr_ne_zero_of_descentHyp (hyp j₀)
  -- Turn each on-curve point into an actual Mordell-Weil group element.
  have hns : ∀ i, (curve c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2 := fun i =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  set g : Fin c.rho → E := fun i => .some (pt i).1 (pt i).2 (hns i) with hg
  -- The certified points are `𝔽₂`-independent under `φ` (they are the rows of the unit matrix `B`).
  have hindep : LinearIndependent (ZMod 2) (fun i => φ (g i)) :=
    linearIndependent_descent hyp pt hns hB hBlen hMlen hinv φ hφ g hg
  -- The finitely generated subgroup `H = ⟨P₁, …, P_ρ⟩` and the restricted data.
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g) with hH
  have hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  set gH : Fin c.rho → H := fun i => ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩ with hgH
  set φH : H →+ (Fin c.rho → ZMod 2) := φ.comp H.subtype.toAddMonoidHom with hφH
  -- The `2`-torsion of `H` is bounded by the curve's, hence by `2^t`.
  have htorH : Nat.card (Submodule.torsionBy ℤ H 2) ≤ 2 ^ c.t :=
    (card_torsionBy_le c.a₂ c.a₄ c.a₆ H).trans htors
  -- Assemble the deduction: `ρ ≤ finrank H + t`, hence `ρ - t ≤ finrank H`.
  have hbound : c.rho ≤ Module.finrank ℤ H + c.t := RankDeduction.rank_ge_le gH φH hindep htorH
  exact ⟨H, hHfin, Nat.sub_le_iff_le_add.mpr hbound⟩

/-- `l.getD n d` is a genuine member of `l` when the index is in range. -/
private theorem getD_mem_of_lt {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- Given a certificate `c` whose short model `curve c.a₂ c.a₄ c.a₆` is the change-of-variables
target of the general model `toCurveQ a₁ a₂ a₃ a₄ a₆` (the equation `hmodel`), and the referee facts
of `rank_ge_of_certificate`, the Mordell-Weil rank of `toCurveQ a₁ a₂ a₃ a₄ a₆` over `ℚ` is at least
`c.rho`. -/
theorem hasRankGE_of_certificate (a₁ a₂ a₃ a₄ a₆ : ℤ) (c : Certificate)
    (hmodel : intShortModel a₁ a₂ a₃ a₄ a₆ = curve c.a₂ c.a₄ c.a₆)
    (hlenP : c.points.length = c.rho)
    (hlenL : c.labels.length = c.rho)
    (hlenB : c.matB.length = c.rho)
    (hlenM : c.matM.length = c.rho)
    (hpt : checkPoints 0 c.a₂ 0 c.a₄ c.a₆ c.points = true)
    (hlabP : checkPrimes c.labels = true)
    (hlabC : checkLabels c.a₂ c.a₄ c.a₆ c.labels = true)
    (hB : checkB c.a₂ c.a₄ c.a₆ c.labels c.matB c.points = true)
    (hinv : F2Invert.checkInv c.rho c.matB c.matM = true)
    (htors : Nat.card {P : (curve c.a₂ c.a₄ c.a₆).toAffine.Point // P + P = 0} ≤ 2 ^ c.t) :
    HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) (c.rho - c.t) := by
  -- The point/label families the soundness theorem consumes are read from the certificate's lists
  -- by `getD`.  Every kernel-checked hypothesis above is `List`-based; the families here appear
  -- only in the (non-computational) proof.
  have hmemP : ∀ i : Fin c.rho, c.points.getD i.val (0, 0) ∈ c.points :=
    fun i => getD_mem_of_lt (by rw [hlenP]; exact i.isLt)
  have hmemL : ∀ j : Fin c.rho, c.labels.getD j.val (0, 0) ∈ c.labels :=
    fun j => getD_mem_of_lt (by rw [hlenL]; exact j.isLt)
  have hcurve : curve c.a₂ c.a₄ c.a₆ = toCurveQ 0 c.a₂ 0 c.a₄ c.a₆ := by
    simp only [curve, toCurveQ, Int.cast_zero]
  rw [checkPoints_iff] at hpt
  have hpt' : ∀ i : Fin c.rho, (curve c.a₂ c.a₄ c.a₆).toAffine.Equation
      (c.points.getD i.val (0, 0)).1 (c.points.getD i.val (0, 0)).2 := by
    intro i
    rw [hcurve]
    exact hpt _ (hmemP i)
  have hlabP' : ∀ j : Fin c.rho, ((c.labels.getD j.val (0, 0)).1).Prime :=
    fun j => checkPrimes_true hlabP _ (hmemL j)
  have hlabC' : ∀ j : Fin c.rho, checkLabel c.a₂ c.a₄ c.a₆
      (c.labels.getD j.val (0, 0)).1 (c.labels.getD j.val (0, 0)).2 = true :=
    fun j => checkLabels_true hlabC _ (hmemL j)
  have key : HasRankGE (curve c.a₂ c.a₄ c.a₆) (c.rho - c.t) :=
    rank_ge_of_certificate c (fun i => c.points.getD i.val (0, 0))
      (fun j => c.labels.getD j.val (0, 0)) hpt' hlabP' hlabC'
      (checkB_true hlenB hlenP hlenL hB) hlenB hlenM hinv htors
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
