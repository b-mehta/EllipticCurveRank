/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certificate
import ECCompute.Check.ColumnCheck
import ECCompute.Check.Points
import ECCompute.Check.Primes
import ECCompute.Check.CheckMatrix
import ECCompute.Check.QuickRfl
import ECCompute.Check.Torsion
import ECCompute.Math.Descent
import ECCompute.Math.LambdaCompute
import ECCompute.Math.RankDeduction
import ECCompute.Math.ModelChange
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.NormNum.Prime

/-!
# The main theory: a rank lower bound from a certificate

This file is the mathematical heart of ECCompute.  It assembles every certified piece into the
statement that a passing certificate forces a lower bound on the Mordell–Weil rank of an elliptic
curve over `ℚ`, and it delivers that bound for a *general* integral Weierstrass model.

The rank lower bound is packaged as `ECCompute.HasRankGE W n`: *there is a finitely generated
`ℤ`-submodule `H` of `W(ℚ)` with `n ≤ finrank ℤ H`.*  Because the rank of any subgroup bounds the
rank of the ambient group from below, this is exactly `rank W(ℚ) ≥ n`, phrased without needing the
Mordell–Weil theorem (`W(ℚ)` is never proven finitely generated).

Two theorems build the bound:

* `rank_ge_of_certificate` proves it on the **short integral model** `curve c.a₂ c.a₄ c.a₆`, where
  the descent character lives.  It chains the certified pieces — descent hypotheses from
  `checkLabel`, the character matrix identity from `lambdaCompute`, `𝔽₂`-linear independence of the
  rows of an invertible matrix, the torsion witness, and the rank deduction.
* `hasRankGE_of_certificate` is the **front door for a general model** `toCurveQ a₁ … a₆`:
  `ModelChange.generalToShortEquiv` carries it to the short model by completing the square and
  scaling, and `hasRankGE_of_addEquiv` transports the bound back along that isomorphism.  Each
  instantiation supplies only the certificate data, the referee facts, and the single equation
  identifying the certificate's short model with the change-of-variables target.
-/

namespace ECCompute

open WeierstrassCurve Module ModelIso ModelChange

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

/-- `l.getD n d` is a genuine member of `l` when the index is in range. -/
private theorem getD_mem_of_lt {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- **The certified rank lower bound for a general integral model.**  Given a certificate `c` whose
short model `curve c.a₂ c.a₄ c.a₆` is the change-of-variables target of the general model
`toCurveQ a₁ a₂ a₃ a₄ a₆` (the equation `hmodel`), and the six referee facts of
`rank_ge_of_certificate`, the Mordell–Weil rank of `toCurveQ a₁ a₂ a₃ a₄ a₆` over `ℚ` is at least
`c.rho - c.t`.  The bound is proven on the short model and transported along
`generalToShortEquiv`. -/
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
    (ht : c.t = 0)
    (htorP : c.torsionPrime ≠ 0)
    (htor : hasRootMod (4 * c.a₂) (16 * c.a₄) (64 * c.a₆) c.torsionPrime = false) :
    HasRankGE (toCurveQ a₁ a₂ a₃ a₄ a₆) (c.rho - c.t) := by
  -- The point/label families the soundness theorem consumes are read from the certificate's lists
  -- by `getD`.  Every kernel-checked hypothesis above is `List`-based, so the kernel never reduces
  -- a `Fin c.rho → _` function; the families here appear only in the (non-computational) proof.
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
      (checkB_true hlenB hlenP hlenL hB) hlenB hlenM hinv ht htorP htor
  exact hasRankGE_of_addEquiv (generalToShortEquiv a₁ a₂ a₃ a₄ a₆) (hmodel.symm ▸ key)

end ECCompute
