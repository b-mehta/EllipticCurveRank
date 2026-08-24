/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Roots of the 2-torsion polynomial

For a Weierstrass curve `W` over a field of characteristic different from `2` with nonzero
discriminant, this file identifies the roots of `W.twoTorsionPolynomial` with the `X`-coordinates
of the nonzero `2`-torsion affine points of `W`.

## Main results

* `WeierstrassCurve.isRoot_twoTorsionPolynomial_iff`: `x` is a root of `W.twoTorsionPolynomial`
  if and only if it is the `X`-coordinate of a nonzero affine point `P` with `P + P = 0`.
-/

section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- Evaluate the 2-torsion polynomial at `x`, expanded via the `bᵢ` coefficients. -/
@[grind =]
public lemma eval_twoTorsionPolynomial_toPoly (x : F) :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPolynomial, Cubic.toPoly]

/-- A nonzero affine point `some x y h` with `P + P = 0` satisfies `y = W.negY x y`. -/
public theorem Y_eq_negY_of_add_self [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0) :
    y = W.toAffine.negY x y := by
  by_contra hne
  rw [Affine.Point.add_self_of_Y_ne hne] at hP
  exact Affine.Point.some_ne_zero _ hP

/-- A nonzero affine `2`-torsion point `some x y h` of `W` (with `P + P = 0`) has `X`-coordinate a
root of `W.twoTorsionPolynomial`. -/
public theorem isRoot_twoTorsionPolynomial_of_add_self [DecidableEq F] {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hP : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0) :
    W.twoTorsionPolynomial.toPoly.IsRoot x := by
  rw [IsRoot.def, eval_twoTorsionPolynomial_toPoly, b₂, b₄, b₆]
  have hy : y = W.toAffine.negY x y := Y_eq_negY_of_add_self W h hP
  rw [Affine.negY] at hy
  have he : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hy
  have heq := h.left
  rw [Affine.equation_iff] at heq
  linear_combination (2 * y + W.a₁ * x + W.a₃) * he - 4 * heq

/-- `x` is a root of the `2`-torsion polynomial of a Weierstrass curve of characteristic
different from `2` with nonzero discriminant if and only if it is the `X`-coordinate of a nonzero
affine `2`-torsion point. -/
public theorem isRoot_twoTorsionPolynomial_iff [DecidableEq F] (h2 : (2 : F) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x : F) :
    W.twoTorsionPolynomial.toPoly.IsRoot x ↔
      ∃ y, ∃ h : W.toAffine.Nonsingular x y,
        (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0 := by
  refine ⟨fun hroot ↦ ?_, fun ⟨y, hns, hP⟩ ↦ isRoot_twoTorsionPolynomial_of_add_self W hns hP⟩
  have h4 : (4 : F) ≠ 0 := by
    have h22 : (4 : F) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  rw [IsRoot.def, eval_twoTorsionPolynomial_toPoly, b₂, b₄, b₆] at hroot
  obtain ⟨y, he⟩ : ∃ y : F, 2 * y + W.a₁ * x + W.a₃ = 0 :=
    ⟨(-W.a₁ * x - W.a₃) / 2, by field_simp; ring⟩
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    have h4G : (4 : F) * (y ^ 2 + W.a₁ * x * y + W.a₃ * y
        - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
      linear_combination (2 * y + W.a₁ * x + W.a₃) * he - hroot
    linear_combination (mul_eq_zero.mp h4G).resolve_left h4
  exact ⟨y, (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq,
    Affine.Point.add_self_of_Y_eq (by rw [Affine.negY]; linear_combination he)⟩

end WeierstrassCurve

end
