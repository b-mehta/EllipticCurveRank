/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.ModelIso
import ECCompute.Check.Fold

/-!
# Point-on-curve check

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
-/

namespace ECCompute.ModelIso

open WeierstrassCurve

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

/-! ## Worked example

The running example is `y² + xy + y = x³` (`a₁ = a₃ = 1`, `a₂ = a₄ = a₆ = 0`). The point
`(x, y) = (0, 0)` lies on it, and the certificate reduces to `true` in the kernel by `rfl`. -/

/-- The point `(0, 0)` is on `y² + xy + y = x³`, checked by kernel `rfl`. -/
example : chkZ 1 0 1 0 0 0 0 = true := rfl

/-- Hence `(0, 0)` satisfies the affine Weierstrass equation, from the `rfl` certificate. -/
example : (toCurveQ 1 0 1 0 0).toAffine.Equation 0 0 :=
  (chkZ_iff 1 0 1 0 0 0 0).mp rfl

end ECCompute.ModelIso
