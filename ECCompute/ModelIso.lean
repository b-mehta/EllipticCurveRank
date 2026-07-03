/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import ECCompute.Fold

/-!
# Points on the curve and the completing-the-square model isomorphism

This file supplies two ingredients an auditor needs when checking a rank certificate.

## Point-on-curve check

`chkZ` is a kernel-reducible `Bool` function that decides, for integer Weierstrass coefficients
`a₁ a₂ a₃ a₄ a₆ : ℤ` and a rational point `(x, y) : ℚ × ℚ`, whether the general Weierstrass
equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
holds in `ℚ`. The check is performed with exact integer arithmetic: it clears the denominators of
`x` and `y` and compares the two sides as integers, so it reduces in the kernel by `rfl` using only
GMP-backed `Int` operations (no `Rat.add`/`Rat.mul`, which are `@[irreducible]` and do not reduce).
`chkZ_iff` is the correctness lemma: the checker returns `true` if and only if the point satisfies
`(toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x y`. `checkPoints` lifts the check to a list of
points.

## The completing-the-square isomorphism

The running example is a general Weierstrass model (`a₁ = a₃ = 1`), but the descent character is
stated for a short model `y² = x³ + a₂'x² + a₄'x + a₆'`. Over `ℚ` (characteristic `≠ 2`) the
substitution `y ↦ y − (a₁x + a₃)/2` — the change of variables `⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩`
of `WeierstrassCurve.VariableChange` — carries the general model to a short one. `shortModel` is
that short model, `shortModel_a₁`/`shortModel_a₃` confirm its linear coefficients vanish, and
`equation_completeSquare` is the isomorphism at the level of the defining equations: `(x, y)` lies
on the general model iff `(x, y + (a₁x + a₃)/2)` lies on the short model.

Rank is an isomorphism invariant of the Mordell–Weil group, so a rank lower bound proven on the
short model transfers back to the general model; see `nonempty_pointAddEquiv`.
-/

namespace ECCompute.ModelIso

open WeierstrassCurve

/-- The general Weierstrass model over `ℚ` with integer coefficients `a₁ a₂ a₃ a₄ a₆`, cast to `ℚ`.
This is the curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. -/
def toCurveQ (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  ⟨(a₁ : ℚ), (a₂ : ℚ), (a₃ : ℚ), (a₄ : ℚ), (a₆ : ℚ)⟩

/-! ## Point-on-curve check -/

/-- Kernel-reducible point-on-curve check. Writing `x = xn/xd` and `y = yn/yd` in lowest terms, the
Weierstrass equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` is equivalent, after clearing the
denominator `xd³·yd²`, to an identity between integers; `chkZ` tests that identity with GMP-backed
`Int` arithmetic, so it reduces in the kernel by `rfl`. -/
def chkZ (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) : Bool :=
  let xn := x.num; let xd := (x.den : ℤ); let yn := y.num; let yd := (y.den : ℤ)
  yn ^ 2 * xd ^ 3 + a₁ * xn * yn * xd ^ 2 * yd + a₃ * yn * xd ^ 3 * yd
    == xn ^ 3 * yd ^ 2 + a₂ * xn ^ 2 * xd * yd ^ 2 + a₄ * xn * xd ^ 2 * yd ^ 2
        + a₆ * xd ^ 3 * yd ^ 2

/-- **Correctness lemma.** The kernel-reducible checker `chkZ` returns `true` if and only if the
point `(x, y)` satisfies the affine Weierstrass equation of `toCurveQ a₁ a₂ a₃ a₄ a₆`. -/
theorem chkZ_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    chkZ a₁ a₂ a₃ a₄ a₆ x y = true ↔
      (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x y := by
  simp only [WeierstrassCurve.Affine.equation_iff, toCurveQ, chkZ, beq_iff_eq]
  have hxd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
  have hx : (x.num : ℚ) = x * x.den := (div_eq_iff hxd).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * y.den := (div_eq_iff hyd).mp (Rat.num_div_den y)
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hxd) (pow_ne_zero _ hyd)
  rw [← @Int.cast_inj ℚ]
  push_cast
  rw [hx, hy]
  refine ⟨fun h => mul_left_cancel₀ hD ?_, fun h => ?_⟩
  · linear_combination h
  · linear_combination (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 * h

/-- The correctness lemma phrased with the raw Weierstrass equation rather than `Equation`. -/
theorem chkZ_iff_raw (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    chkZ a₁ a₂ a₃ a₄ a₆ x y = true ↔
      y ^ 2 + (a₁ : ℚ) * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by
  simp only [chkZ_iff, WeierstrassCurve.Affine.equation_iff, toCurveQ]

/-- Check that every point in a list lies on `toCurveQ a₁ a₂ a₃ a₄ a₆`. Kernel-reducible: a
structural `allList` fold, so the kernel peels one point at a time, never indexing positionally. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  allList (fun p => chkZ a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

/-- `checkPoints` returns `true` if and only if every listed point satisfies the equation. -/
theorem checkPoints_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) :
    checkPoints a₁ a₂ a₃ a₄ a₆ pts = true ↔
      ∀ p ∈ pts, (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation p.1 p.2 := by
  simp only [checkPoints, allList_eq_true, chkZ_iff]

/-! ## The completing-the-square model isomorphism -/

/-- The change of variables `⟨u, r, s, t⟩ = ⟨1, 0, -a₁/2, -a₃/2⟩` completing the square: the
substitution `y ↦ y − (a₁x + a₃)/2` (over `ℚ`, where `2` is invertible) that clears the `a₁` and
`a₃` coefficients. -/
def completeSquare (a₁ a₃ : ℤ) : VariableChange ℚ :=
  ⟨1, 0, -(a₁ : ℚ) / 2, -(a₃ : ℚ) / 2⟩

/-- The short model `y² = x³ + a₂'x² + a₄'x + a₆'` obtained from `toCurveQ a₁ a₂ a₃ a₄ a₆` by
completing the square. Its `a₁` and `a₃` coefficients vanish (`shortModel_a₁`, `shortModel_a₃`). -/
def shortModel (a₁ a₂ a₃ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  completeSquare a₁ a₃ • toCurveQ a₁ a₂ a₃ a₄ a₆

@[simp]
theorem shortModel_a₁ (a₁ a₂ a₃ a₄ a₆ : ℤ) : (shortModel a₁ a₂ a₃ a₄ a₆).a₁ = 0 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₁, inv_one,
    Units.val_one]
  ring

@[simp]
theorem shortModel_a₂ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).a₂ = (a₂ : ℚ) + (a₁ : ℚ) ^ 2 / 4 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₂, inv_one,
    Units.val_one, one_pow]
  ring

@[simp]
theorem shortModel_a₃ (a₁ a₂ a₃ a₄ a₆ : ℤ) : (shortModel a₁ a₂ a₃ a₄ a₆).a₃ = 0 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₃, inv_one,
    Units.val_one, one_pow]
  ring

@[simp]
theorem shortModel_a₄ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).a₄ = (a₄ : ℚ) + (a₁ : ℚ) * a₃ / 2 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₄, inv_one,
    Units.val_one, one_pow]
  ring

@[simp]
theorem shortModel_a₆ (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).a₆ = (a₆ : ℚ) + (a₃ : ℚ) ^ 2 / 4 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₆, inv_one,
    Units.val_one, one_pow]
  ring

/-- **The completing-the-square isomorphism, on the defining equations.** A rational point `(x, y)`
lies on the general model `toCurveQ a₁ a₂ a₃ a₄ a₆` if and only if `(x, y + (a₁x + a₃)/2)` lies on
the short model `shortModel a₁ a₂ a₃ a₄ a₆`. This is the bijection of affine solution loci
underlying the model isomorphism. -/
theorem equation_completeSquare (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x y ↔
      (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Equation x (y + ((a₁ : ℚ) * x + a₃) / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [shortModel_a₁, shortModel_a₂, shortModel_a₃, shortModel_a₄, shortModel_a₆, toCurveQ]
  constructor <;> intro h <;> linear_combination h

section GroupIso

open WeierstrassCurve.Affine

variable (a₁ a₂ a₃ a₄ a₆ : ℤ)

/-- Elementary disjunction fact underlying the transfer of the nonsingular condition: the two
partial-derivative non-vanishing conditions on the general and short models are related by the
invertible substitution `(F_X, F_Y) ↦ (F_X - σ F_Y, F_Y)`. -/
private theorem or_ne_zero_sub_iff (A B σ : ℚ) :
    (A ≠ 0 ∨ B ≠ 0) ↔ (A - σ * B ≠ 0 ∨ B ≠ 0) := by
  by_cases hB : B = 0 <;> simp [hB]

/-- Two affine points with equal coordinates are equal (nonsingularity proofs are irrelevant). -/
private theorem point_some_congr {C : WeierstrassCurve ℚ} {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : C.toAffine.Nonsingular x₁ y₁} {h₂ : C.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : C.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/-- **Nonsingularity transfers along the completing-the-square substitution.** A point `(x, y)` is
nonsingular on the general model iff `(x, y + (a₁x + a₃)/2)` is nonsingular on the short model. -/
theorem nonsingular_completeSquare (x y : ℚ) :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Nonsingular x y ↔
      (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Nonsingular x (y + ((a₁ : ℚ) * x + a₃) / 2) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.nonsingular_iff',
    ← equation_completeSquare]
  refine and_congr_right fun _ => ?_
  have e1 : (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.a₁ * (y + ((a₁ : ℚ) * x + a₃) / 2)
        - (3 * x ^ 2 + 2 * (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.a₂ * x
            + (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.a₄)
      = ((toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₁ * y
          - (3 * x ^ 2 + 2 * (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₂ * x
              + (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₄))
        - (a₁ : ℚ) / 2 * (2 * y + (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₁ * x
            + (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₃) := by
    simp only [shortModel_a₁, shortModel_a₂, shortModel_a₄, toCurveQ]; ring
  have e2 : 2 * (y + ((a₁ : ℚ) * x + a₃) / 2) + (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.a₁ * x
        + (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.a₃
      = 2 * y + (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₁ * x
        + (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.a₃ := by
    simp only [shortModel_a₁, shortModel_a₃, toCurveQ]; ring
  rw [e1, e2]
  exact or_ne_zero_sub_iff _ _ _

/-- The `Y`-negation commutes with the completing-the-square shift. -/
theorem negY_completeSquare (x y : ℚ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.negY x (y + ((a₁ : ℚ) * x + a₃) / 2)
      = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.negY x y + ((a₁ : ℚ) * x + a₃) / 2 := by
  simp only [WeierstrassCurve.Affine.negY, shortModel_a₁, shortModel_a₃, toCurveQ]; ring

/-- The `X`-coordinate of the sum is unchanged by the shift (the slope shifts by `a₁/2`). -/
theorem addX_completeSquare (x₁ x₂ ℓ : ℚ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.addX x₁ x₂ (ℓ + (a₁ : ℚ) / 2)
      = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.addX x₁ x₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, shortModel_a₁, shortModel_a₂, toCurveQ]; ring

/-- The `Y`-coordinate of the sum commutes with the shift. -/
theorem addY_completeSquare (x₁ x₂ y₁ ℓ : ℚ) :
    (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.addY x₁ x₂ (y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2)
        (ℓ + (a₁ : ℚ) / 2)
      = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ
        + ((a₁ : ℚ) * (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₃) / 2 := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, shortModel_a₁, shortModel_a₂,
    shortModel_a₃, toCurveQ]
  ring

/-- The slope commutes with the shift, up to the additive constant `a₁/2` coming from the
straightening of the tangent/secant line. Requires both points to lie on the general model and to be
in the non-degenerate branch of the addition law. -/
theorem slope_completeSquare (x₁ x₂ y₁ y₂ : ℚ)
    (h₁ : (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.negY x₂ y₂)) :
    (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.slope x₁ x₂ (y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2)
        (y₂ + ((a₁ : ℚ) * x₂ + a₃) / 2)
      = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ + (a₁ : ℚ) / 2 := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hyeq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst hx
    subst hyeq
    have hy' : y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2
        ≠ (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.negY x₁ (y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2) := by
      rw [negY_completeSquare]
      intro hcontra
      exact hy (add_right_cancel hcontra)
    have hDval : y₁ - (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.negY x₁ y₁
        = 2 * y₁ + (a₁ : ℚ) * x₁ + (a₃ : ℚ) := by
      simp only [WeierstrassCurve.Affine.negY, toCurveQ]; ring
    have hDval' : (y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2)
          - (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.negY x₁ (y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2)
        = 2 * y₁ + (a₁ : ℚ) * x₁ + (a₃ : ℚ) := by
      simp only [WeierstrassCurve.Affine.negY, shortModel_a₁, shortModel_a₃]; ring
    have hden : 2 * y₁ + (a₁ : ℚ) * x₁ + (a₃ : ℚ) ≠ 0 := hDval ▸ sub_ne_zero.mpr hy
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, hDval, hDval', div_add' _ _ _ hden,
      div_eq_div_iff hden hden]
    simp only [shortModel_a₁, shortModel_a₂, shortModel_a₄, toCurveQ]
    ring
  · rw [slope_of_X_ne hx, slope_of_X_ne hx, div_add' _ _ _ (sub_ne_zero.mpr hx),
      div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hx)]
    ring

/-- Forward coordinate map on Mordell–Weil groups: `(x, y) ↦ (x, y + (a₁x + a₃)/2)`. -/
def fwd :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point → (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some x (y + ((a₁ : ℚ) * x + a₃) / 2) ((nonsingular_completeSquare a₁ a₂ a₃ a₄ a₆ x y).mp h)

/-- Inverse coordinate map: `(x, y) ↦ (x, y - (a₁x + a₃)/2)`. -/
def bwd :
    (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point → (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    .some x (y - ((a₁ : ℚ) * x + a₃) / 2)
      ((nonsingular_completeSquare a₁ a₂ a₃ a₄ a₆ x (y - ((a₁ : ℚ) * x + a₃) / 2)).mpr
        (by simpa using h))

@[simp] theorem fwd_some (x y : ℚ)
    (h : (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Nonsingular x y) :
    fwd a₁ a₂ a₃ a₄ a₆ (.some x y h)
      = .some x (y + ((a₁ : ℚ) * x + a₃) / 2)
        ((nonsingular_completeSquare a₁ a₂ a₃ a₄ a₆ x y).mp h) :=
  rfl

@[simp] theorem bwd_some (x y : ℚ)
    (h : (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Nonsingular x y) :
    bwd a₁ a₂ a₃ a₄ a₆ (.some x y h)
      = .some x (y - ((a₁ : ℚ) * x + a₃) / 2)
        ((nonsingular_completeSquare a₁ a₂ a₃ a₄ a₆ x (y - ((a₁ : ℚ) * x + a₃) / 2)).mpr
          (by simpa using h)) :=
  rfl

/-- The forward map is additive: it commutes with the affine group law on both models. -/
theorem fwd_map_add (P Q : (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point) :
    fwd a₁ a₂ a₃ a₄ a₆ (P + Q) = fwd a₁ a₂ a₃ a₄ a₆ P + fwd a₁ a₂ a₃ a₄ a₆ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hycond : y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2
        = (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.negY x₂ (y₂ + ((a₁ : ℚ) * x₂ + a₃) / 2) := by
      rw [negY_completeSquare, ← hy, hx]
    rw [Point.add_of_Y_eq hx hy, fwd_some, fwd_some, Point.add_of_Y_eq hx hycond]
    rfl
  · have hxy' : ¬(x₁ = x₂ ∧ y₁ + ((a₁ : ℚ) * x₁ + a₃) / 2
        = (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.negY x₂ (y₂ + ((a₁ : ℚ) * x₂ + a₃) / 2)) := by
      rintro ⟨hx, hy⟩
      refine hxy ⟨hx, ?_⟩
      rw [negY_completeSquare, hx] at hy
      exact add_right_cancel hy
    have hℓ := slope_completeSquare a₁ a₂ a₃ a₄ a₆ x₁ x₂ y₁ y₂ h₁.left h₂.left hxy
    rw [Point.add_some hxy]
    simp only [fwd_some]
    rw [Point.add_some hxy']
    refine point_some_congr ?_ ?_
    · rw [hℓ, addX_completeSquare]
    · rw [hℓ, addY_completeSquare]

/-- **Rank is an isomorphism invariant.** The completing-the-square change of variables `y ↦
y + (a₁x + a₃)/2` induces a group isomorphism between the Mordell–Weil groups of the general model
`toCurveQ a₁ a₂ a₃ a₄ a₆` and the short model `shortModel a₁ a₂ a₃ a₄ a₆`, so any rank lower bound
proven on the short model transfers back to the general model.

The bijection of affine loci is `equation_completeSquare`/`nonsingular_completeSquare`; the
group-law compatibility (`fwd_map_add`) is the substantive content: it reduces, on unfolding the
affine addition, to the facts that negation (`negY_completeSquare`), the slope
(`slope_completeSquare`), and the sum coordinates (`addX_completeSquare`, `addY_completeSquare`) all
commute with the shift. -/
theorem nonempty_pointAddEquiv :
    Nonempty ((toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point ≃+
      (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point) :=
  ⟨AddEquiv.mk'
    ⟨fwd a₁ a₂ a₃ a₄ a₆, bwd a₁ a₂ a₃ a₄ a₆,
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [fwd_some, bwd_some]; exact point_some_congr rfl (by ring),
      fun P => by
        rcases P with _ | ⟨x, y, h⟩
        · rfl
        · rw [bwd_some, fwd_some]; exact point_some_congr rfl (by ring)⟩
    (fwd_map_add a₁ a₂ a₃ a₄ a₆)⟩

end GroupIso

/-! ## Worked example

The running example is `y² + xy + y = x³` (`a₁ = a₃ = 1`, `a₂ = a₄ = a₆ = 0`). The point
`(x, y) = (0, 0)` lies on it, and the certificate reduces to `true` in the kernel by `rfl`. -/

/-- The point `(0, 0)` is on `y² + xy + y = x³`, checked by kernel `rfl`. -/
example : chkZ 1 0 1 0 0 0 0 = true := rfl

/-- Hence `(0, 0)` satisfies the affine Weierstrass equation, from the `rfl` certificate. -/
example : (toCurveQ 1 0 1 0 0).toAffine.Equation 0 0 :=
  (chkZ_iff 1 0 1 0 0 0 0).mp rfl

end ECCompute.ModelIso
