/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.Repr
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Algebra.Field.ZMod

/-!
# The reduction map on affine points

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` of good reduction at a prime `p`, this file
defines the reduction map `red_p` on affine points, sending `P = (x, y)` to the affine point
underlying `ℤ → ZMod p` applied to its integer representative `Trep x y w`.

## Main declarations

* `ECCompute.red_p`: the reduction map.
* `ECCompute.red_p_zero`: `red_p 0 = 0`.
* `ECCompute.red_p_of_den_zero`: `red_p (x, y) = 0` when `p ∣ x.den`.
* `ECCompute.red_p_of_den_ne`: `red_p (x, y) = (x̄, ȳ)` when `p ∤ x.den`.
-/

open WeierstrassCurve

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]

/-! ### Coordinates of the reduced representative -/

variable {x y : ℚ} {w : ℕ}

/-- The reduced `X`-coordinate of `Trep x y w` is `x.num · w`. -/
private theorem Trep_map_zero :
    ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 0 = (x.num : ZMod p) * (w : ZMod p) := by
  simp only [Function.comp_apply, Trep, Matrix.cons_val_zero, eq_intCast]
  push_cast
  grind

/-- The reduced `Y`-coordinate of `Trep x y w` is `y.num`. -/
private theorem Trep_map_one :
    ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 1 = (y.num : ZMod p) := by
  simp only [Function.comp_apply, Trep, Matrix.cons_val_one, Matrix.cons_val_zero, eq_intCast]

/-- The reduced `Z`-coordinate of `Trep x y w` is `w³`. -/
private theorem Trep_map_two :
    ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 = (w : ZMod p) ^ 3 := by
  simp only [Function.comp_apply, Trep, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    eq_intCast]
  push_cast
  grind

/-- The affine `x`-coordinate of the reduced representative is `(x : ZMod p)`. -/
private theorem Trep_coord_zero (hden : x.den = w ^ 2) (hwne : (w : ZMod p) ≠ 0) :
    ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 0 / ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2
      = (x : ZMod p) := by
  rw [Trep_map_zero, Trep_map_two, Rat.cast_def, hden]
  grind

/-- The affine `y`-coordinate of the reduced representative is `(y : ZMod p)`. -/
private theorem Trep_coord_one (hden' : y.den = w ^ 3) (hwne : (w : ZMod p) ≠ 0) :
    ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 1 / ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2
      = (y : ZMod p) := by
  rw [Trep_map_one, Trep_map_two, Rat.cast_def, hden']
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 3 hwne) (pow_ne_zero 3 hwne)]

/-- The reduced discriminant is nonzero (good reduction transported to `ZMod p`). -/
private theorem map_Δ_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).Δ ≠ 0 := by
  rw [WeierstrassCurve.map_Δ]; simpa [eq_intCast] using hΔ

/-! ### Nonsingularity of the reduced representative -/

/-- The reduced integer representative is a nonsingular projective point of the reduced curve. -/
theorem red_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      ((Int.castRingHom (ZMod p)) ∘ Trep x y w) := by
  have hEq : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Equation
      ((Int.castRingHom (ZMod p)) ∘ Trep x y w) :=
    (Trep_equation a₂ a₄ a₆ h.1 hden hden').map (Int.castRingHom (ZMod p))
  by_cases hwz : (w : ZMod p) = 0
  · -- `z = 0`: the point reduces to the origin.
    have hz0 : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 = 0 := by grind [Trep_map_two]
    rw [Projective.nonsingular_of_Z_eq_zero hz0]
    refine ⟨hEq, Or.inr ?_⟩
    have hX0 : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 0 = 0 :=
      Projective.X_eq_zero_of_Z_eq_zero hEq hz0
    have hYne : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 1 ≠ 0 := by
      rw [Trep_map_one, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hpy
      have hp : p.Prime := Fact.out
      have hpw : p ∣ w := (ZMod.natCast_eq_zero_iff w p).mp hwz
      have hpw3 : (p : ℤ) ∣ (w : ℤ) ^ 3 :=
        (Int.natCast_dvd_natCast.mpr hpw).trans (dvd_pow_self _ three_ne_zero)
      have hunit : IsUnit (p : ℤ) := (Trep_primitive hden').isUnit_of_dvd' hpy hpw3
      have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
      grind [Int.isUnit_iff]
    rw [hX0]
    simpa using pow_ne_zero 2 hYne
  · -- `z ≠ 0`: good reduction makes it nonsingular.
    have hzne : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 ≠ 0 := by
      rw [Trep_map_two]; exact pow_ne_zero 3 hwz
    rw [Projective.nonsingular_of_Z_ne_zero hzne]
    exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (map_Δ_ne a₂ a₄ a₆ p hΔ)).mp ((Projective.equation_of_Z_ne_zero hzne).mp hEq)

/-! ### The reduction map -/

open Classical in
/-- The reduction map on affine points: `P ↦` the affine point underlying `ℤ → ZMod p` applied
to the integer representative `Trep` of `P`. Requires good reduction (`hΔ`). -/
noncomputable def red_p (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point
  | .zero => 0
  | .some _ _ h =>
      Projective.Point.toAffineLift
        ⟨(Projective.nonsingularLift_iff _).mpr
          (red_nonsingular a₂ a₄ a₆ p hΔ h
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2)⟩

/-- The reduction map sends the origin to the origin. -/
@[simp]
theorem red_p_zero (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    red_p a₂ a₄ a₆ p hΔ 0 = 0 :=
  rfl

/-- When `p ∣ x.den` the representative has vanishing `z`-coordinate, so the point reduces to the
origin. -/
theorem red_p_of_den_zero (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    red_p a₂ a₄ a₆ p hΔ (.some x y h) = 0 := by
  set w := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose
  have hden : x.den = w ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
  have hwz : (w : ZMod p) = 0 := (Rat.den_cast_eq_zero_iff two_ne_zero hden).mp hd
  have hz0 : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 = 0 := by grind [Trep_map_two]
  simp only [red_p]
  exact Projective.Point.toAffineLift_of_Z_eq_zero _ hz0

/-- The reduced affine coordinates lie on the reduced curve and are nonsingular. -/
theorem red_nonsingular_affine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3)
    (hwne : (w : ZMod p) ≠ 0) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Nonsingular
      (x : ZMod p) (y : ZMod p) := by
  have hns := red_nonsingular a₂ a₄ a₆ p hΔ h hden hden'
  have hzne : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 ≠ 0 := by
    rw [Trep_map_two]; exact pow_ne_zero 3 hwne
  rw [Projective.nonsingular_of_Z_ne_zero hzne] at hns
  rwa [Trep_coord_zero p hden hwne, Trep_coord_one p hden' hwne] at hns

/-- When `p ∤ x.den` the point reduces to the affine point with the reduced coordinates
`(x : ZMod p, y : ZMod p)`. -/
theorem red_p_of_den_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    red_p a₂ a₄ a₆ p hΔ (.some x y h)
      = .some (x : ZMod p) (y : ZMod p)
          (red_nonsingular_affine a₂ a₄ a₆ p hΔ h
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2
            (mt (Rat.den_cast_eq_zero_iff two_ne_zero
              (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1).mpr hd)) := by
  set w := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose
  have hden : x.den = w ^ 2 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
  have hden' : y.den = w ^ 3 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2
  have hwne : (w : ZMod p) ≠ 0 := mt (Rat.den_cast_eq_zero_iff two_ne_zero hden).mpr hd
  have hzne : ((Int.castRingHom (ZMod p)) ∘ Trep x y w) 2 ≠ 0 := by
    rw [Trep_map_two]; exact pow_ne_zero 3 hwne
  simp only [red_p]
  rw [Projective.Point.toAffineLift_of_Z_ne_zero hzne]
  simp only [Trep_coord_zero p hden hwne, Trep_coord_one p hden' hwne]

end ECCompute
