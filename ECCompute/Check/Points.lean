/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Theory.CompleteSquare
import ECCompute.Check.Fold

/-!
# Point-on-curve check

`chkZ` is a kernel-reducible `Bool` function that decides, for integer Weierstrass coefficients
`a₁ a₂ a₃ a₄ a₆ : ℤ` and a rational point `(x, y) : ℚ × ℚ`, whether the Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` holds in `ℚ`. `chkZ_iff` is the correctness lemma;
`checkPoints` lifts the check to a list of points.
-/

namespace ECCompute

open WeierstrassCurve

/-- Kernel-reducible point-on-curve check. Writing `x = xn/xd` and `y = yn/yd` in lowest terms, the
Weierstrass equation is equivalent, after clearing the denominator `xd³·yd²`, to an identity between
integers, which `chkZ` tests. -/
noncomputable def chkZ (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) : Bool :=
  let xn := x.num; let xd := (x.den : ℤ)
  let yn := y.num; let yd := (y.den : ℤ)
  let xd2 := Int.mul xd xd; let xd3 := Int.mul xd2 xd
  let yd2 := Int.mul yd yd
  let xn2 := Int.mul xn xn; let xn3 := Int.mul xn2 xn
  let yn2 := Int.mul yn yn
  Int.beq'
    (Int.add (Int.add (Int.mul yn2 xd3)
        (Int.mul (Int.mul (Int.mul (Int.mul a₁ xn) yn) xd2) yd))
      (Int.mul (Int.mul (Int.mul a₃ yn) xd3) yd))
    (Int.add (Int.add (Int.add (Int.mul xn3 yd2)
        (Int.mul (Int.mul (Int.mul a₂ xn2) xd) yd2))
        (Int.mul (Int.mul (Int.mul a₄ xn) xd2) yd2))
      (Int.mul (Int.mul a₆ xd3) yd2))

/-- The kernel-reducible checker `chkZ` returns `true` if and only if the point `(x, y)` satisfies
the affine Weierstrass equation of the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
theorem chkZ_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) :
    chkZ a₁ a₂ a₃ a₄ a₆ x y = true ↔
      (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation x y := by
  have hmul : ∀ a b : ℤ, Int.mul a b = a * b := fun _ _ => rfl
  have hadd : ∀ a b : ℤ, Int.add a b = a + b := fun _ _ => rfl
  simp only [WeierstrassCurve.Affine.equation_iff, chkZ, Int.beq'_eq, hmul, hadd]
  have hxd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
  have hx : (x.num : ℚ) = x * x.den := (div_eq_iff hxd).mp (Rat.num_div_den x)
  have hy : (y.num : ℚ) = y * y.den := (div_eq_iff hyd).mp (Rat.num_div_den y)
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hxd) (pow_ne_zero _ hyd)
  rw [← @Int.cast_inj ℚ]
  push_cast
  rw [hx, hy]
  exact ⟨fun h => mul_left_cancel₀ hD (by grind), fun h => by grind⟩

/-- Check that every point in a list lies on the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  allList (fun p => chkZ a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

/-- `checkPoints` returns `true` if and only if every listed point satisfies the equation. -/
theorem checkPoints_iff (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) :
    checkPoints a₁ a₂ a₃ a₄ a₆ pts = true ↔
      ∀ p ∈ pts, (⟨a₁, a₂, a₃, a₄, a₆⟩ : WeierstrassCurve ℚ).toAffine.Equation p.1 p.2 := by
  simp only [checkPoints, allList_eq_true, chkZ_iff]

/-! ## Worked example

The running example is `y² + xy + y = x³` (`a₁ = a₃ = 1`, `a₂ = a₄ = a₆ = 0`). The point
`(x, y) = (0, 0)` lies on it, and the certificate reduces to `true` in the kernel by `rfl`. -/

/-- The point `(0, 0)` is on `y² + xy + y = x³`, checked by kernel `rfl`. -/
example : chkZ 1 0 1 0 0 0 0 = true := rfl

/-- Hence `(0, 0)` satisfies the affine Weierstrass equation, from the `rfl` certificate. -/
example : (⟨1, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Equation 0 0 :=
  (chkZ_iff 1 0 1 0 0 0 0).mp rfl

end ECCompute
