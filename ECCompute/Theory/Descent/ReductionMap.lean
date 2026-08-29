/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Theory.Model
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import ECCompute.Theory.Descent.PointArith
public import ECCompute.ForMathlib.RatDenom
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# The reduction map on affine points

For a point `P = (x, y)` on the integral curve `y² = x³ + a₂x² + a₄x + a₆` and a prime `p`, this
file builds the integer projective representative `intRep x y w = ![x.num·w, y.num, w³]` (where
`x.den = w²`, `y.den = w³`), applies `ℤ → ZMod p` to it to get the `ZMod p`-projective
representative `repr`, and takes its affine point to define the reduction map `redP`.

## Main declarations

* `ECCompute.intRep`: the integer representative `![x.num · w, y.num, w³]`.
* `ECCompute.repr`: the `ZMod p`-projective representative of an affine point.
* `ECCompute.redP`: the reduction map, `toAffine` of `repr`.
* `ECCompute.redP_of_den_zero`: `redP (x, y) = 0` when `p ∣ x.den`.
* `ECCompute.redP_of_den_ne`: `redP (x, y) = (x̄, ȳ)` when `p ∤ x.den`.
-/

open WeierstrassCurve Projective

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}

/-! ### The integer projective representative -/

/-- The integer projective representative `![x.num · w, y.num, w³]` of the affine point
`(x, y)`, where `w` is the square-root witness of the denominators (`x.den = w²`, `y.den = w³`).
Over `ℚ` this is `w³ • [x : y : 1]` (see `intRep_map_ℚ`). -/
public def intRep (x y : ℚ) (w : ℕ) : Fin 3 → ℤ := ![x.num * w, y.num, w ^ 3]

/-- The image of `curve` under `ℤ → ℚ`, in projective form, is the rational curve. -/
theorem map_curve_toProjective :
    (curve a₂ a₄ a₆).toProjective.map (Int.castRingHom ℚ) = (curveQ a₂ a₄ a₆).toProjective :=
  map_curveQ

variable {x y : ℚ} {w : ℕ}

/-- Over `ℚ`, the integer representative equals `w³ • [x : y : 1]`. -/
public theorem intRep_map_ℚ (hxden : x.den = w ^ 2) (hyden : y.den = w ^ 3) :
    Int.castRingHom ℚ ∘ intRep x y w = (w ^ 3 : ℚ) • ![x, y, 1] := by
  simp [intRep, comp_fin3, ← Rat.mul_den_eq_num, hxden, hyden]
  grind

/-- The integer representative lies on the integral projective curve. -/
theorem intRep_equation (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curve a₂ a₄ a₆).toProjective.Equation (intRep x y w) := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rwa [← map_equation _ (Int.castRingHom ℚ).injective_int, intRep_map_ℚ hden hden',
    equation_smul _ (isUnit_iff_ne_zero.2 (by positivity)), equation_some,
    map_curve_toProjective]

/-- The three coordinates of `intRep x y w`. -/
@[simp] theorem intRep_zero : intRep x y w 0 = x.num * w := by simp [intRep]

@[simp] theorem intRep_one : intRep x y w 1 = y.num := by simp [intRep]

@[simp] theorem intRep_two : intRep x y w 2 = w ^ 3 := by simp [intRep]

variable {p : ℕ}

/-! ### Coordinates of the reduced representative -/

section
variable [Fact p.Prime]

theorem intRep_coord_zero (hden : x.den = w ^ 2) (hwne : (w : ZMod p) ≠ 0) :
    (Int.castRingHom (ZMod p) ∘ intRep x y w) 0
      / (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = x := by
  simp [field, Rat.cast_def, hden]

theorem intRep_coord_one (hden' : y.den = w ^ 3) :
    (Int.castRingHom (ZMod p) ∘ intRep x y w) 1
      / (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = y := by
  simp [field, Rat.cast_def, hden']

end

/-- The reduced discriminant is nonzero (good reduction transported to `ZMod p`). -/
theorem map_Δ_ne (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curveZMod a₂ a₄ a₆ p).Δ ≠ 0 := by
  simpa [WeierstrassCurve.baseChange, map_Δ, eq_intCast] using hΔ

/-! ### Nonsingularity of the reduced representative -/

/-- The reduced integer representative is a nonsingular projective point of the reduced curve. -/
theorem red_nonsingular (hp : p.Prime) (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ intRep x y w) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEq : (curveZMod a₂ a₄ a₆ p).toProjective.Equation
      (Int.castRingHom (ZMod p) ∘ intRep x y w) :=
    (intRep_equation h.1 hden hden').map (Int.castRingHom (ZMod p))
  by_cases hwz : (w : ZMod p) = 0
  · -- `z = 0`: the point reduces to the origin.
    have hz0 : (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = 0 := by simp [hwz]
    rw [nonsingular_of_Z_eq_zero hz0]
    refine ⟨hEq, Or.inr ?_⟩
    have hYne : (Int.castRingHom (ZMod p) ∘ intRep x y w) 1 ≠ 0 := by
      simp only [Function.comp_apply, intRep_one, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hpy
      have hpw3 : (p : ℤ) ∣ (y.den : ℤ) := by
        rwa [Int.natCast_dvd_natCast, hden', hp.prime.dvd_pow_iff_dvd three_ne_zero,
          ← ZMod.natCast_eq_zero_iff]
      grind [Int.isUnit_iff, y.isCoprime_num_den.isUnit_of_dvd' hpy hpw3, hp.two_le]
    rw [X_eq_zero_of_Z_eq_zero hEq hz0]
    simpa using pow_ne_zero 2 hYne
  · -- `z ≠ 0`: good reduction makes it nonsingular.
    rw [nonsingular_of_Z_ne_zero (by simp [hwz])]
    exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (map_Δ_ne hΔ)).mp ((equation_of_Z_ne_zero (by simp [hwz])).mp hEq)

section
variable [Fact p.Prime]

/-! ### The projective representative -/

/-- The fixed `ZMod p`-projective representative of an affine point: `![0, 1, 0]` for the origin,
and `ℤ → ZMod p` applied to the integer representative `intRep` otherwise. -/
public noncomputable def repr (p : ℕ) [Fact p.Prime] :
    (curveQ a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h => Int.castRingHom (ZMod p) ∘ intRep x y (den_isSquare h.1).choose

/-- `repr` of the origin is the fixed representative `![0, 1, 0]`. -/
public theorem repr_zero : repr p (.zero : (curveQ a₂ a₄ a₆).toAffine.Point) = ![0, 1, 0] := by
  simp [repr]

/-- `repr` of a `some` point, through any witness `w` with `x.den = w²`, `y.den = w³`. -/
public theorem repr_some (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    repr p (.some x y h) = Int.castRingHom (ZMod p) ∘ intRep x y w := by
  obtain rfl : w = (den_isSquare h.1).choose :=
    Nat.pow_left_injective two_ne_zero (hden.symm.trans (den_isSquare h.1).choose_spec.1)
  rfl

/-- `repr P` is a nonsingular representative on the reduced curve (needs good reduction `hΔ`). -/
public theorem repr_nonsingular (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (repr p P) := by
  cases P with
  | zero => exact nonsingular_zero
  | some x y h =>
    obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
    rw [repr_some h hden hden']
    exact red_nonsingular Fact.out hΔ h hden hden'

/-! ### The reduction map -/

/-- The reduction map on affine points: the affine point of the reduced projective
representative `repr`. -/
public noncomputable def redP (p : ℕ) [Fact p.Prime]
    (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point :=
  Point.toAffine (curveZMod a₂ a₄ a₆ p).toProjective (repr p P)

/-- `redP` is `toAffine` of the fixed representative. -/
public theorem redP_eq_toAffine (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    redP p P = Point.toAffine (curveZMod a₂ a₄ a₆ p).toProjective (repr p P) := by simp only [redP]

@[simp]
public theorem redP_zero : redP p (0 : (curveQ a₂ a₄ a₆).toAffine.Point) = 0 := by
  rw [redP_eq_toAffine]; exact Point.toAffine_zero

/-- When `p ∣ x.den` the representative has vanishing `z`-coordinate, so the point reduces to the
origin. -/
public theorem redP_of_den_zero (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hd : (x.den : ZMod p) = 0) :
    redP p (.some x y h) = 0 := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  rw [redP_eq_toAffine, repr_some h hden hden']
  exact Point.toAffine_of_Z_eq_zero (by simpa [hden] using hd)

/-- The reduced affine coordinates lie on the reduced curve and are nonsingular. -/
public theorem red_nonsingular_affine (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  have hwne : (w : ZMod p) ≠ 0 := by simpa [hden] using hd
  have hns := red_nonsingular Fact.out hΔ h hden hden'
  rwa [nonsingular_of_Z_ne_zero (by simp [hwne]), intRep_coord_zero hden hwne,
    intRep_coord_one hden'] at hns

/-- When `p ∤ x.den` the point reduces to the affine point with the reduced coordinates
`(x : ZMod p, y : ZMod p)`. -/
public theorem redP_of_den_ne (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    redP p (.some x y h)
      = .some x y (red_nonsingular_affine hΔ h hd) := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  have hwne : (w : ZMod p) ≠ 0 := by simpa [hden] using hd
  have hns := red_nonsingular Fact.out hΔ h hden hden'
  rw [redP_eq_toAffine, repr_some h hden hden', Point.toAffine_of_Z_ne_zero hns (by simp [hwne])]
  simp only [intRep_coord_zero hden hwne, intRep_coord_one hden']

end

end ECCompute
