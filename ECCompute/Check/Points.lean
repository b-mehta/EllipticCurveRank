/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Check.Fold
import Mathlib.Data.Rat.Defs

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
  let xd2 := xd.mul xd; let xd3 := xd2.mul xd
  let yd2 := yd.mul yd
  let xn2 := xn.mul xn; let xn3 := xn2.mul xn
  let yn2 := yn.mul yn
  (((yn2.mul xd3).add ((((a₁.mul xn).mul yn).mul xd2).mul yd)).add
      (((a₃.mul yn).mul xd3).mul yd)).beq'
    ((((xn3.mul yd2).add (((a₂.mul xn2).mul xd).mul yd2)).add
        (((a₄.mul xn).mul xd2).mul yd2)).add ((a₆.mul xd3).mul yd2))

/-- Check that every point in a list lies on the model `⟨a₁, a₂, a₃, a₄, a₆⟩`. -/
noncomputable def checkPoints (a₁ a₂ a₃ a₄ a₆ : ℤ) (pts : List (ℚ × ℚ)) : Bool :=
  allList (fun p => checkPoint a₁ a₂ a₃ a₄ a₆ p.1 p.2) pts

end ECCompute
