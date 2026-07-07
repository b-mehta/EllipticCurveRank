/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# A rank-3 curve with a single rational 2-torsion point

The elliptic curve

  `E : y² = x³ - 82 x`

over `ℚ` has Mordell-Weil rank at least `3`.  Its `2`-division cubic `x³ - 82 x = x (x² - 82)`
has the single rational root `x = 0` (the quadratic cofactor `x² - 82` is irreducible over `ℚ`),
so `E` has exactly one nonzero rational `2`-torsion point `(0, 0)`, i.e. `t = dim_𝔽₂ E(ℚ)[2] = 1`.

The certificate exhibits `ρ = 4` points with `𝔽₂`-independent descent images, and concedes the one
torsion dimension *sharply*: rather than the universal `|E(ℚ)[2]| ≤ 4` bound (which would only give
`rank ≥ ρ - 2 = 2`), it certifies `|E(ℚ)[2]| ≤ 2` by naming the short-model root `R = 0` and the
witness prime `ℓ = 5` at which the cofactor `x² - 1312` has no root, giving the full
`rank ≥ ρ - t = 4 - 1 = 3`.  Points (in short-model coordinates) in `data/rank13.txt`, descent
labels in `data/rank13-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- The `a₄` coefficient of the rank-3 curve. -/
abbrev curve13A₄ : ℤ := -82

/-- The rank-3 curve `y² = x³ - 82 x` over `ℚ`. -/
def curveThirteen : WeierstrassCurve ℚ := toCurveQ 0 0 0 curve13A₄ 0

/-- The rank-3 curve has Mordell-Weil rank at least `3`, with a single rational
`2`-torsion point. -/
theorem curveThirteen_hasRankGE_3 : HasRankGE curveThirteen 3 := by
  unfold curveThirteen curve13A₄
  certify_curve oneTorsion root 0 witness 5
    points "data/rank13.txt" labels "data/rank13-labels.txt"

end ECCompute
