/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Descent.Reduction.Repr
public import ECCompute.Theory.Descent.DenominatorSquare
public import ECCompute.ForMathlib.RatDenom
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# The reduction map on affine points

For an integral curve `y² = x³ + a₂x² + a₄x + a₆` and a prime `p`, this file defines the
`ZMod p`-projective representative `repr` of an affine point, applying `ℤ → ZMod p` to its
integer representative `trep x y w`, and the reduction map `redP`, the affine point of `repr`.

## Main declarations

* `ECCompute.repr`: the `ZMod p`-projective representative of an affine point.
* `ECCompute.redP`: the reduction map, `toAffine` of `repr`.
* `ECCompute.redP_zero`: `redP 0 = 0`.
* `ECCompute.redP_of_den_zero`: `redP (x, y) = 0` when `p ∣ x.den`.
* `ECCompute.redP_of_den_ne`: `redP (x, y) = (x̄, ȳ)` when `p ∤ x.den`.
-/

open WeierstrassCurve Projective

namespace ECCompute

variable (a₂ a₄ a₆ : ℤ) (p : ℕ) [Fact p.Prime]

/-! ### Coordinates of the reduced representative -/

variable {x y : ℚ} {w : ℕ}

theorem trep_coord_zero (hden : x.den = w ^ 2) (hwne : (w : ZMod p) ≠ 0) :
    (Int.castRingHom (ZMod p) ∘ trep x y w) 0 / (Int.castRingHom (ZMod p) ∘ trep x y w) 2
      = (x : ZMod p) := by
  simp only [Function.comp_apply, trep_zero, trep_two, eq_intCast, Rat.cast_def, hden]
  push_cast
  grind

theorem trep_coord_one (hden' : y.den = w ^ 3) (hwne : (w : ZMod p) ≠ 0) :
    (Int.castRingHom (ZMod p) ∘ trep x y w) 1 / (Int.castRingHom (ZMod p) ∘ trep x y w) 2
      = (y : ZMod p) := by
  simp only [Function.comp_apply, trep_one, trep_two, eq_intCast, Rat.cast_def, hden']
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 3 hwne) (pow_ne_zero 3 hwne)]

/-- The reduced discriminant is nonzero (good reduction transported to `ZMod p`). -/
theorem map_Δ_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).Δ ≠ 0 := by
  simpa [map_Δ, eq_intCast] using hΔ

/-! ### Nonsingularity of the reduced representative -/

/-- The reduced integer representative is a nonsingular projective point of the reduced curve. -/
public theorem red_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ trep x y w) := by
  have hEq : ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Equation
      (Int.castRingHom (ZMod p) ∘ trep x y w) :=
    (trep_equation h.1 hden hden').map (Int.castRingHom (ZMod p))
  by_cases hwz : (w : ZMod p) = 0
  · -- `z = 0`: the point reduces to the origin.
    have hz0 : (Int.castRingHom (ZMod p) ∘ trep x y w) 2 = 0 := by simp [hwz]
    rw [nonsingular_of_Z_eq_zero hz0]
    refine ⟨hEq, Or.inr ?_⟩
    have hX0 : (Int.castRingHom (ZMod p) ∘ trep x y w) 0 = 0 :=
      X_eq_zero_of_Z_eq_zero hEq hz0
    have hYne : (Int.castRingHom (ZMod p) ∘ trep x y w) 1 ≠ 0 := by
      simp only [Function.comp_apply, trep_one, eq_intCast]
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hpy
      have hpw : p ∣ w := (ZMod.natCast_eq_zero_iff w p).mp hwz
      have hpw3 : (p : ℤ) ∣ (w : ℤ) ^ 3 :=
        (Int.natCast_dvd_natCast.mpr hpw).trans (dvd_pow_self _ three_ne_zero)
      have hunit : IsUnit (p : ℤ) :=
        y.isCoprime_num_den.isUnit_of_dvd' hpy (by rwa [hden', Nat.cast_pow])
      have h2 : (2 : ℤ) ≤ (p : ℤ) := mod_cast (Fact.out : p.Prime).two_le
      grind [Int.isUnit_iff]
    rw [hX0]
    simpa using pow_ne_zero 2 hYne
  · -- `z ≠ 0`: good reduction makes it nonsingular.
    have hzne : (Int.castRingHom (ZMod p) ∘ trep x y w) 2 ≠ 0 := by
      simpa using pow_ne_zero 3 hwz
    rw [nonsingular_of_Z_ne_zero hzne]
    exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (map_Δ_ne a₂ a₄ a₆ p hΔ)).mp ((equation_of_Z_ne_zero hzne).mp hEq)

/-! ### The projective representative -/

/-- The fixed `ZMod p`-projective representative of an affine point: `![0, 1, 0]` for the origin,
and `ℤ → ZMod p` applied to the integer representative `trep` otherwise. -/
public noncomputable def repr : (curve a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h =>
      Int.castRingHom (ZMod p) ∘ trep x y (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose

/-- `repr` of a `some` point, through any witness `w` with `x.den = w²`, `y.den = w³`. -/
public theorem repr_some (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    repr a₂ a₄ a₆ p (.some x y h) = Int.castRingHom (ZMod p) ∘ trep x y w := by
  obtain rfl : w = (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose := by
    have h1 := (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
    exact Nat.pow_left_injective two_ne_zero (hden.symm.trans h1)
  rfl

/-- `repr P` is a nonsingular representative on the reduced curve (needs good reduction `hΔ`). -/
public theorem repr_nonsingular (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curve a₂ a₄ a₆).toAffine.Point) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective.Nonsingular
      (repr a₂ a₄ a₆ p P) := by
  cases P with
  | zero => exact nonsingular_zero
  | some x y h =>
      obtain ⟨w, hden, hden'⟩ := den_isSquare_of_nonsingular a₂ a₄ a₆ h
      rw [repr_some a₂ a₄ a₆ p h hden hden']
      exact red_nonsingular a₂ a₄ a₆ p hΔ h hden hden'

/-! ### The reduction map -/

/-- The reduction map on affine points: the affine point of the reduced projective
representative `repr`. -/
public noncomputable def redP (P : (curve a₂ a₄ a₆).toAffine.Point) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Point :=
  Point.toAffine
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective (repr a₂ a₄ a₆ p P)

/-- `redP` is `toAffine` of the fixed representative. -/
public theorem redP_eq_toAffine (P : (curve a₂ a₄ a₆).toAffine.Point) :
    redP a₂ a₄ a₆ p P
      = Point.toAffine
          ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective (repr a₂ a₄ a₆ p P) := by
  simp only [redP]

@[simp]
public theorem redP_zero : redP a₂ a₄ a₆ p 0 = 0 := by
  rw [redP_eq_toAffine]; exact Point.toAffine_zero

/-- `redP` on a `some` point, through any witness `w` with `x.den = w²`, `y.den = w³`. -/
public theorem redP_some (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    redP a₂ a₄ a₆ p (.some x y h)
      = Point.toAffine
          ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toProjective
          (Int.castRingHom (ZMod p) ∘ trep x y w) := by
  rw [redP_eq_toAffine, repr_some a₂ a₄ a₆ p h hden hden']

/-- When `p ∣ x.den` the representative has vanishing `z`-coordinate, so the point reduces to the
origin. -/
public theorem redP_of_den_zero (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hd : ¬ Rat.IsPIntegral p x) :
    redP a₂ a₄ a₆ p (.some x y h) = 0 := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare_of_nonsingular a₂ a₄ a₆ h
  have hwz : (w : ZMod p) = 0 := (Rat.den_cast_eq_zero_iff two_ne_zero hden).mp
    (by by_contra hne; exact hd (Rat.mem_padicInteger_iff.mpr hne))
  have hz0 : (Int.castRingHom (ZMod p) ∘ trep x y w) 2 = 0 := by simp [hwz]
  rw [redP_some a₂ a₄ a₆ p h hden hden']
  exact Point.toAffine_of_Z_eq_zero hz0

/-- The reduced affine coordinates lie on the reduced curve and are nonsingular. -/
public theorem red_nonsingular_affine (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3)
    (hd : Rat.IsPIntegral p x) :
    ((curveℤ a₂ a₄ a₆).map (Int.castRingHom (ZMod p))).toAffine.Nonsingular
      (x : ZMod p) (y : ZMod p) := by
  have hwne : (w : ZMod p) ≠ 0 := Rat.pow_base_ne_of_pIntegral hd hden two_ne_zero
  have hns := red_nonsingular a₂ a₄ a₆ p hΔ h hden hden'
  have hzne : (Int.castRingHom (ZMod p) ∘ trep x y w) 2 ≠ 0 := by
    simpa using pow_ne_zero 3 hwne
  rw [nonsingular_of_Z_ne_zero hzne] at hns
  rwa [trep_coord_zero p hden hwne, trep_coord_one p hden' hwne] at hns

/-- When `p ∤ x.den` the point reduces to the affine point with the reduced coordinates
`(x : ZMod p, y : ZMod p)`. -/
public theorem redP_of_den_ne (hΔ : ((curveℤ a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curve a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : Rat.IsPIntegral p x) :
    redP a₂ a₄ a₆ p (.some x y h)
      = .some (x : ZMod p) (y : ZMod p)
          (red_nonsingular_affine a₂ a₄ a₆ p hΔ h
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.1
            (den_isSquare_of_nonsingular a₂ a₄ a₆ h).choose_spec.2 hd) := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare_of_nonsingular a₂ a₄ a₆ h
  have hwne : (w : ZMod p) ≠ 0 := Rat.pow_base_ne_of_pIntegral hd hden two_ne_zero
  have hzne : (Int.castRingHom (ZMod p) ∘ trep x y w) 2 ≠ 0 := by
    simpa using pow_ne_zero 3 hwne
  rw [redP_some a₂ a₄ a₆ p h hden hden',
    Point.toAffine_of_Z_ne_zero (red_nonsingular a₂ a₄ a₆ p hΔ h hden hden') hzne]
  simp only [trep_coord_zero p hden hwne, trep_coord_one p hden' hwne]

end ECCompute
