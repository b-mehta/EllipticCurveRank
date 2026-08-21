/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Check.Fold

/-!
# Point-on-curve check

`checkPoint` is a kernel-reducible `Bool` that decides, for integer Weierstrass coefficients
`a₁ a₂ a₃ a₄ a₆ : ℤ` and a rational point `(x, y) : ℚ × ℚ`, whether the Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` holds in `ℚ`. `checkPoints` lifts the check to a list of
points. Correctness is `ECCompute.checkPoint_iff` / `ECCompute.checkPoints_iff` in
`ECCompute.Soundness.Points`.
-/

namespace ECCompute

/-- Kernel-reducible point-on-curve check. Writing `x = xn/xd` and `y = yn/yd` in lowest terms, the
Weierstrass equation is equivalent, after clearing the denominator `xd³·yd²`, to an identity between
integers, which `checkPoint` tests. -/
noncomputable def checkPoint (a₁ a₂ a₃ a₄ a₆ : ℤ) (x y : ℚ) : Bool :=
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

/-- Check that every point in a list lies on the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  allList (fun p => checkPoint a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

end ECCompute
