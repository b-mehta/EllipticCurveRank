/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

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
`chkZ_iff` is the bridge lemma: the checker returns `true` if and only if the point satisfies
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

/-- **Bridge lemma.** The kernel-reducible checker `chkZ` returns `true` if and only if the point
`(x, y)` satisfies the affine Weierstrass equation of `toCurveQ a₁ a₂ a₃ a₄ a₆`. -/
theorem chkZ_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    chkZ a₁ a₂ a₃ a₄ a₆ x y = true ↔
      (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [toCurveQ, chkZ]
  rw [beq_iff_eq]
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

/-- The bridge lemma phrased with the raw Weierstrass equation rather than `Equation`. -/
theorem chkZ_iff_raw (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    chkZ a₁ a₂ a₃ a₄ a₆ x y = true ↔
      y ^ 2 + (a₁ : ℚ) * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by
  rw [chkZ_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [toCurveQ]

/-- Check that every point in a list lies on `toCurveQ a₁ a₂ a₃ a₄ a₆`. Kernel-reducible. -/
def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  pts.all fun p => chkZ a₁ a₂ a₃ a₄ a₆ p.1 p.2

/-- `checkPoints` returns `true` if and only if every listed point satisfies the equation. -/
theorem checkPoints_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) :
    checkPoints a₁ a₂ a₃ a₄ a₆ pts = true ↔
      ∀ p ∈ pts, (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation p.1 p.2 := by
  simp only [checkPoints, List.all_eq_true, chkZ_iff]

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
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₁]
  ring

@[simp]
theorem shortModel_a₃ (a₁ a₂ a₃ a₄ a₆ : ℤ) : (shortModel a₁ a₂ a₃ a₄ a₆).a₃ = 0 := by
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₃]
  ring

/-- **The completing-the-square isomorphism, on the defining equations.** A rational point `(x, y)`
lies on the general model `toCurveQ a₁ a₂ a₃ a₄ a₆` if and only if `(x, y + (a₁x + a₃)/2)` lies on
the short model `shortModel a₁ a₂ a₃ a₄ a₆`. This is the bijection of affine solution loci
underlying the model isomorphism. -/
theorem equation_completeSquare (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    (toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Equation x y ↔
      (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Equation x (y + ((a₁ : ℚ) * x + a₃) / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [shortModel, completeSquare, toCurveQ, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    inv_one, Units.val_one, one_pow]
  constructor <;> intro h <;> linear_combination h

/-- **Rank is an isomorphism invariant.** The completing-the-square change of variables induces a
group isomorphism between the Mordell–Weil groups of the general model and the short model, so any
rank lower bound proven on the short model transfers back to the general model.

The coordinate-level content of this isomorphism — that `y ↦ y + (a₁x + a₃)/2` is a bijection of the
defining Weierstrass loci — is proven in `equation_completeSquare`. Upgrading it to an `AddEquiv`
additionally requires that the affine group law is preserved by the substitution. Mathlib does not
yet provide a `VariableChange`-induced isomorphism of `Affine.Point` groups (it has `Point` maps
only for base-change ring homomorphisms), so the group-law compatibility is left as the one
remaining obligation here.

TODO (rank transfer): construct the `AddEquiv` explicitly. Forward map: `Point.zero ↦ Point.zero`
and `Point.some x y h ↦ Point.some x (y + (a₁x + a₃)/2) h'`, with `h'` obtained from
`equation_completeSquare` together with a matching `Nonsingular` transfer; inverse map: subtract the
same shift. `map_add` then reduces to checking that the affine addition formulas
(`WeierstrassCurve.Affine.slope`, `addX`, `addY`) commute with the `s = -a₁/2`, `t = -a₃/2`
substitution — a finite `ring`-style verification once the addition is unfolded on each branch. -/
theorem nonempty_pointAddEquiv (a₁ a₂ a₃ a₄ a₆ : ℤ) :
    Nonempty ((toCurveQ a₁ a₂ a₃ a₄ a₆).toAffine.Point ≃+
      (shortModel a₁ a₂ a₃ a₄ a₆).toAffine.Point) := by
  sorry

/-! ## Worked example

The running example is `y² + xy + y = x³` (`a₁ = a₃ = 1`, `a₂ = a₄ = a₆ = 0`). The point
`(x, y) = (0, 0)` lies on it, and the certificate reduces to `true` in the kernel by `rfl`. -/

/-- The point `(0, 0)` is on `y² + xy + y = x³`, checked by kernel `rfl`. -/
example : chkZ 1 0 1 0 0 0 0 = true := rfl

/-- Hence `(0, 0)` satisfies the affine Weierstrass equation, from the `rfl` certificate. -/
example : (toCurveQ 1 0 1 0 0).toAffine.Equation 0 0 :=
  (chkZ_iff 1 0 1 0 0 0 0).mp rfl

end ECCompute.ModelIso
