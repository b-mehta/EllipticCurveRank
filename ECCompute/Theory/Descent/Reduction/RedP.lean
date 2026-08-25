/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.Descent.Reduction.Repr
import ECCompute.ForMathlib.RatDenom
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# The reduction map on affine points

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` of good reduction at a prime `p`, this file
defines the reduction map `redP` on affine points, sending `P = (x, y)` to the affine point
underlying `ℤ → ZMod p` applied to its integer representative `trep x y w`.

## Main declarations

* `ECCompute.redP`: the reduction map.
* `ECCompute.redP_zero`: `redP 0 = 0`.
* `ECCompute.redP_of_den_zero`: `redP (x, y) = 0` when `p ∣ x.den`.
* `ECCompute.redP_of_den_ne`: `redP (x, y) = (x̄, ȳ)` when `p ∤ x.den`.
-/

open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} [Fact p.Prime]

/-! ### Coordinates of the reduced representative -/

variable {x y : ℚ} {w : ℕ}

private theorem trep_map_zero :
    ((Int.castRingHom (ZMod p)) ∘ trep x y w) 0 = (x.num : ZMod p) * (w : ZMod p) := by
  simp only [Function.comp_apply, trep, Matrix.cons_val_zero, eq_intCast]
  push_cast
  grind

private theorem trep_map_one :
    ((Int.castRingHom (ZMod p)) ∘ trep x y w) 1 = (y.num : ZMod p) := by
  simp only [Function.comp_apply, trep, Matrix.cons_val_one, Matrix.cons_val_zero, eq_intCast]

private theorem trep_map_two :
    ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 = (w : ZMod p) ^ 3 := by
  simp only [Function.comp_apply, trep, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    eq_intCast]
  push_cast
  grind

private theorem trep_coord_zero (hden : x.den = w ^ 2) (hwne : (w : ZMod p) ≠ 0) :
    ((Int.castRingHom (ZMod p)) ∘ trep x y w) 0 / ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2
      = (x : ZMod p) := by
  rw [trep_map_zero, trep_map_two, Rat.cast_def, hden]
  grind

private theorem trep_coord_one (hden' : y.den = w ^ 3) (hwne : (w : ZMod p) ≠ 0) :
    ((Int.castRingHom (ZMod p)) ∘ trep x y w) 1 / ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2
      = (y : ZMod p) := by
  rw [trep_map_one, trep_map_two, Rat.cast_def, hden']
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 3 hwne) (pow_ne_zero 3 hwne)]

/-- The reduced discriminant is nonzero (good reduction transported to `ZMod p`). -/
private theorem map_Δ_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).Δ ≠ 0 := by
  rw [map_Δ]; simpa [eq_intCast] using hΔ

/-! ### Nonsingularity of the reduced representative -/

/-- The reduced integer representative is a nonsingular projective point of the reduced curve. -/
theorem red_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      ((Int.castRingHom (ZMod p)) ∘ trep x y w) := by
  have hEq : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Equation
      ((Int.castRingHom (ZMod p)) ∘ trep x y w) :=
    (trep_equation h.1 hden hden').map (Int.castRingHom (ZMod p))
  by_cases hwz : (w : ZMod p) = 0
  · -- `z = 0`: the point reduces to the origin.
    have hz0 : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 = 0 := by grind [trep_map_two]
    rw [Projective.nonsingular_of_Z_eq_zero hz0]
    refine ⟨hEq, Or.inr ?_⟩
    have hX0 : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 0 = 0 :=
      Projective.X_eq_zero_of_Z_eq_zero hEq hz0
    have hYne : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 1 ≠ 0 := by
      rw [trep_map_one, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hpy
      have hp : p.Prime := Fact.out
      have hpw : p ∣ w := (ZMod.natCast_eq_zero_iff w p).mp hwz
      have hpw3 : (p : ℤ) ∣ (w : ℤ) ^ 3 :=
        (Int.natCast_dvd_natCast.mpr hpw).trans (dvd_pow_self _ three_ne_zero)
      have hunit : IsUnit (p : ℤ) := (trep_primitive hden').isUnit_of_dvd' hpy hpw3
      have h2 : (2 : ℤ) ≤ (p : ℤ) := mod_cast hp.two_le
      grind [Int.isUnit_iff]
    rw [hX0]
    simpa using pow_ne_zero 2 hYne
  · -- `z ≠ 0`: good reduction makes it nonsingular.
    have hzne : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 ≠ 0 := by
      rw [trep_map_two]; exact pow_ne_zero 3 hwz
    rw [Projective.nonsingular_of_Z_ne_zero hzne]
    exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (map_Δ_ne hΔ)).mp ((Projective.equation_of_Z_ne_zero hzne).mp hEq)

/-! ### The reduction map -/

open Classical in
/-- The reduction map on affine points: `P ↦` the affine point underlying `ℤ → ZMod p` applied
to the integer representative `trep` of `P`. Requires good reduction (`hΔ`). -/
noncomputable def redP (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]
    (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curve a₂ a₄ a₆).toAffine.Point →
      ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point
  | .zero => 0
  | .some _ _ h =>
      Projective.Point.toAffineLift
        ⟨(Projective.nonsingularLift_iff _).mpr
          (red_nonsingular hΔ h
            (den_isSquare_of_nonsingular h).choose_spec.1
            (den_isSquare_of_nonsingular h).choose_spec.2)⟩

@[simp]
theorem redP_zero (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    redP a₂ a₄ a₆ p hΔ 0 = 0 :=
  rfl

/-- When `p ∣ x.den` the representative has vanishing `z`-coordinate, so the point reduces to the
origin. -/
theorem redP_of_den_zero (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    redP a₂ a₄ a₆ p hΔ (.some x y h) = 0 := by
  set w := (den_isSquare_of_nonsingular h).choose
  have hden : x.den = w ^ 2 := (den_isSquare_of_nonsingular h).choose_spec.1
  have hwz : (w : ZMod p) = 0 := (Rat.den_cast_eq_zero_iff two_ne_zero hden).mp hd
  have hz0 : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 = 0 := by grind [trep_map_two]
  simp only [redP]
  exact Projective.Point.toAffineLift_of_Z_eq_zero _ hz0

/-- The reduced affine coordinates lie on the reduced curve and are nonsingular. -/
theorem red_nonsingular_affine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3)
    (hwne : (w : ZMod p) ≠ 0) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Nonsingular
      (x : ZMod p) (y : ZMod p) := by
  have hns := red_nonsingular hΔ h hden hden'
  have hzne : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 ≠ 0 := by
    rw [trep_map_two]; exact pow_ne_zero 3 hwne
  rw [Projective.nonsingular_of_Z_ne_zero hzne] at hns
  rwa [trep_coord_zero hden hwne, trep_coord_one hden' hwne] at hns

/-- When `p ∤ x.den` the point reduces to the affine point with the reduced coordinates
`(x : ZMod p, y : ZMod p)`. -/
theorem redP_of_den_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    redP a₂ a₄ a₆ p hΔ (.some x y h)
      = .some (x : ZMod p) (y : ZMod p)
          (red_nonsingular_affine hΔ h
            (den_isSquare_of_nonsingular h).choose_spec.1
            (den_isSquare_of_nonsingular h).choose_spec.2
            (mt (Rat.den_cast_eq_zero_iff two_ne_zero
              (den_isSquare_of_nonsingular h).choose_spec.1).mpr hd)) := by
  set w := (den_isSquare_of_nonsingular h).choose
  have hden : x.den = w ^ 2 := (den_isSquare_of_nonsingular h).choose_spec.1
  have hden' : y.den = w ^ 3 := (den_isSquare_of_nonsingular h).choose_spec.2
  have hwne : (w : ZMod p) ≠ 0 := mt (Rat.den_cast_eq_zero_iff two_ne_zero hden).mpr hd
  have hzne : ((Int.castRingHom (ZMod p)) ∘ trep x y w) 2 ≠ 0 := by
    rw [trep_map_two]; exact pow_ne_zero 3 hwne
  simp only [redP]
  rw [Projective.Point.toAffineLift_of_Z_ne_zero hzne]
  simp only [trep_coord_zero hden hwne, trep_coord_one hden' hwne]

end ECCompute
