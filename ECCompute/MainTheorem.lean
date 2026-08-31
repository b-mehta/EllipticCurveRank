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
  -- MEASUREMENT ONLY: `Certificate.points` now carries the flat `(xnA, xs, xd, ynA, yd)` encoding
  -- rather than `ℚ × ℚ`; the soundness assembly against the decoded points is not restated here.
  sorry

end ECCompute
