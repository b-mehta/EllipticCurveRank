/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify
import ECCompute.Check.JInvariant

/-!
# A rank-3 curve with a single rational 2-torsion point

The elliptic curve `E : y² = x³ - 82 x` over `ℚ` has Mordell-Weil rank at least `3`.
Its `2`-division cubic factors as `x (x² - 82)`, and `x² - 82` is irreducible over `ℚ`,
so the only nonzero rational `2`-torsion point is `(0, 0)` and `t = dim_𝔽₂ E(ℚ)[2] = 1`.

The certificate gives `ρ = 4` points with `𝔽₂`-independent descent images and bounds
`|E(ℚ)[2]| ≤ 2` from the root `R = 0` and the witness prime `ℓ = 5`, at which `x² - 82`
has no root mod `5`. These combine to `rank ≥ ρ - t = 4 - 1 = 3`. Points (short-model
coordinates) are in `data/rank13.txt`, descent labels in `data/rank13-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of the rank-3 curve. -/
abbrev curve13A₄ : ℚ := -82

/-- The rank-3 curve `y² = x³ - 82 x` over `ℚ`. -/
def curveThirteen : WeierstrassCurve ℚ := ⟨0, 0, 0, curve13A₄, 0⟩

/-- The rank-3 curve has Mordell-Weil rank at least `3`, with a single rational
`2`-torsion point. -/
theorem curveThirteen_hasRankGE_3 : HasRankGE curveThirteen 3 := by
  unfold curveThirteen curve13A₄
  certify_curve oneTorsion root 0 witness 5
    points "data/rank13.txt" labels "data/rank13-labels.txt"

/-- The rank-3 curve is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curveThirteen.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of the rank-3 curve is `1728` (it has complex multiplication by `ℤ[i]`). -/
theorem curveThirteen_j : curveThirteen.j = 1728 := j_eq_of_beq _ 1728 (by quickRfl)

end ECCompute
