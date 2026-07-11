/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify
import ECCompute.Check.JInvariant

/-!
# A rank-4 curve with full rational 2-torsion

The elliptic curve

  `E : y² = x³ - x² - 24649 x + 1355209`

over `ℚ` has Mordell-Weil rank at least `4` (a curve of Wiman, 1945).  Its `2`-division cubic
factors completely, `x³ - x² - 24649 x + 1355209 = (x - 67)(x - 113)(x + 179)`, so `E` has full
rational `2`-torsion `E(ℚ)[2] ≅ (ℤ/2)²`, i.e. `t = 2`, and its discriminant is a perfect square.

This is the first ECCompute deliverable with `t > 0`.  The certificate exhibits `ρ = 6` points with
`𝔽₂`-independent descent images (the four rational points of infinite order plus the two
`2`-torsion points `(67, 0)`, `(113, 0)`), and concedes the two torsion dimensions via the
universal bound `|E(ℚ)[2]| ≤ 4 = 2²`, giving `rank ≥ ρ - t = 6 - 2 = 4`.  Points (in short-model
coordinates) in `data/rank14.txt`, descent labels in `data/rank14-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₂` coefficient of the rank-4 curve. -/
abbrev curve14A₂ : ℚ := -1

/-- The `a₄` coefficient of the rank-4 curve. -/
abbrev curve14A₄ : ℚ := -24649

/-- The `a₆` coefficient of the rank-4 curve. -/
abbrev curve14A₆ : ℚ := 1355209

/-- The rank-4 curve `y² = x³ - x² - 24649 x + 1355209` over `ℚ`. -/
def curveFourteen : WeierstrassCurve ℚ := ⟨0, curve14A₂, 0, curve14A₄, curve14A₆⟩

/-- The rank-4 curve has Mordell-Weil rank at least `4`, despite full rational `2`-torsion. -/
theorem curveFourteen_hasRankGE_4 : HasRankGE curveFourteen 4 := by
  unfold curveFourteen curve14A₂ curve14A₄ curve14A₆
  certify_curve fullTorsion points "data/rank14.txt" labels "data/rank14-labels.txt"

/-- The rank-4 curve is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curveFourteen.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of the rank-4 curve. -/
theorem curveFourteen_j : curveFourteen.j = 404370344147392 / 42649271289 :=
  j_eq_of_beq _ _ (by quickRfl)

end ECCompute
