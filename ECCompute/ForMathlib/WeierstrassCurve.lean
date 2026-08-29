/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Weierstrass curve helpers for mathlib

Negation on affine points when `a₁ = a₃ = 0`, two criteria for equivalence of nonsingular
projective representatives over a field, and the `j`-invariant of a curve with nonzero
discriminant over a field.

## Main results

* `WeierstrassCurve.Affine.negY_of_a₁_a₃_eq_zero`: `negY x y = -y` when `a₁ = a₃ = 0`.
* `WeierstrassCurve.Projective.equiv_of_proportional`: `V 2 • U = U 2 • V` implies `U ≈ V`.
* `WeierstrassCurve.Projective.equiv_of_toAffine_eq`: equal affine points imply `U ≈ V`.
* `WeierstrassCurve.j_eq_iff`: `j = q ↔ c₄³ = Δ · q` for a curve with invertible discriminant.
* `WeierstrassCurve.isElliptic_of_Δ_ne_zero`: `Δ ≠ 0` over a field gives `IsElliptic`.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]

/-- On a Weierstrass curve with `a₁ = a₃ = 0`, negation is `negY x y = -y`. -/
@[grind =]
theorem negY_of_a₁_a₃_eq_zero (W : WeierstrassCurve R) (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    {x y : R} : W.toAffine.negY x y = -y := by simp [negY, ha1, ha3]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Projective

variable {F : Type*} [Field F] {W : Projective F} {U V : Fin 3 → F}

/-- Two nonsingular projective representatives over a field that are proportional with cross
scalars given by each other's `Z`-coordinate are equivalent: if `V 2 • U = U 2 • V`, then
`U ≈ V`. -/
theorem equiv_of_proportional (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (hprop : V 2 • U = U 2 • V) : U ≈ V := by
  have hcU0 := congrFun hprop 0
  have hcU1 := congrFun hprop 1
  simp only [Pi.smul_apply, smul_eq_mul] at hcU0 hcU1
  by_cases hUz : U 2 = 0
  · -- `U z = 0`; deduce `V z = 0`, then both reduce to the point at infinity.
    have hVz : V 2 = 0 := by
      rw [nonsingular_of_Z_eq_zero hUz] at hU
      grind [mul_eq_zero]
    exact Setoid.trans (equiv_zero_of_Z_eq_zero hU hUz)
      (Setoid.symm (equiv_zero_of_Z_eq_zero hV hVz))
  · -- `U z ≠ 0`; deduce `V z ≠ 0` and use `equiv_of_X_eq_of_Y_eq`.
    have hVz : V 2 ≠ 0 := fun hVz ↦ by
      rw [nonsingular_of_Z_eq_zero hVz] at hV
      grind [mul_eq_zero]
    exact equiv_of_X_eq_of_Y_eq hUz hVz (by grind) (by grind)

/-- Two nonsingular projective representatives over a field with the same underlying affine point
are equivalent. See also `toAffine_of_equiv`. -/
theorem equiv_of_toAffine_eq (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (h : Point.toAffine W U = Point.toAffine W V) : U ≈ V := by
  classical
  have hUl : W.NonsingularLift ⟦U⟧ := (nonsingularLift_iff U).mpr hU
  have hVl : W.NonsingularLift ⟦V⟧ := (nonsingularLift_iff V).mpr hV
  have hmk : (⟨hUl⟩ : W.Point) = ⟨hVl⟩ := by
    apply (Point.toAffineAddEquiv W).injective
    rw [Point.toAffineAddEquiv_apply, Point.toAffineAddEquiv_apply,
      Point.toAffineLift_eq, Point.toAffineLift_eq]
    exact h
  exact Quotient.exact (congrArg Point.point hmk)

end WeierstrassCurve.Projective

namespace WeierstrassCurve

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

/-- For a Weierstrass curve with invertible discriminant, `j = q` iff `c₄³ = Δ · q`. -/
theorem j_eq_iff [W.IsElliptic] {q : F} : W.j = q ↔ W.c₄ ^ 3 = W.Δ * q := by
  rw [j, Units.inv_mul_eq_iff_eq_mul, coe_Δ']

/-- Over a field, a nonzero discriminant makes a Weierstrass curve an elliptic curve. -/
theorem isElliptic_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

end WeierstrassCurve
