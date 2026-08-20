/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Roots of the 2-torsion polynomial

For a Weierstrass curve `W` over a field of characteristic different from `2` with nonzero
discriminant, this file identifies the roots of `W.twoTorsionPolynomial` with the `X`-coordinates
of the nonzero `2`-torsion affine points of `W`.

## Main results

* `WeierstrassCurve.isRoot_twoTorsionPolynomial_iff`: `x` is a root of `W.twoTorsionPolynomial`
  if and only if it is the `X`-coordinate of a nonzero affine point `P` with `P + P = 0`.
-/

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- Evaluate the 2-torsion polynomial at `x`, expanded via the `bᵢ` coefficients. -/
@[grind =]
lemma eval_twoTorsionPolynomial_toPoly (x : F) :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPolynomial, Cubic.toPoly]

/-- `x` is a root of the `2`-torsion polynomial of a Weierstrass curve of characteristic
different from `2` with nonzero discriminant if and only if it is the `X`-coordinate of a nonzero
affine `2`-torsion point. -/
theorem isRoot_twoTorsionPolynomial_iff [DecidableEq F] (h2 : (2 : F) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x : F) :
    W.twoTorsionPolynomial.toPoly.IsRoot x ↔
      ∃ y, ∃ h : W.toAffine.Nonsingular x y,
        (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0 := by
  have h4 : (4 : F) ≠ 0 := by
    have h22 : (4 : F) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  rw [IsRoot.def, eval_twoTorsionPolynomial_toPoly, b₂, b₄, b₆]
  constructor
  · intro hroot
    obtain ⟨y, he⟩ : ∃ y : F, 2 * y + W.a₁ * x + W.a₃ = 0 :=
      ⟨(-W.a₁ * x - W.a₃) / 2, by field_simp; ring⟩
    have heq : W.toAffine.Equation x y := by
      rw [Affine.equation_iff]
      have h4G : (4 : F) * (y ^ 2 + W.a₁ * x * y + W.a₃ * y
          - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
        linear_combination (2 * y + W.a₁ * x + W.a₃) * he - hroot
      linear_combination (mul_eq_zero.mp h4G).resolve_left h4
    refine ⟨y, (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq,
      Affine.Point.add_self_of_Y_eq ?_⟩
    rw [Affine.negY]
    linear_combination he
  · rintro ⟨y, hns, hP⟩
    have hy : y = W.toAffine.negY x y := by
      by_contra hne
      rw [Affine.Point.add_self_of_Y_ne hne] at hP
      exact Affine.Point.some_ne_zero _ hP
    rw [Affine.negY] at hy
    have he : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hy
    have heq := hns.left
    rw [Affine.equation_iff] at heq
    linear_combination (2 * y + W.a₁ * x + W.a₃) * he - 4 * heq

end WeierstrassCurve
