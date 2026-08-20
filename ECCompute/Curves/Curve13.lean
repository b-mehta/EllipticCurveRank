/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify
import ECCompute.Check.JInvariant

/-!
# Curve 13 has rank at least 3, with a single rational 2-torsion point

The elliptic curve recorded as
[curve 13](https://elliptic-rank.icarm.cloud/curve/13) on the ICARM Elliptic Curve Rank
Leaderboard is `E : y² = x³ - 82 x` over `ℚ`, of Mordell-Weil rank at least `3`.
Its `2`-division cubic factors as `x (x² - 82)`, and `x² - 82` is irreducible over `ℚ`,
so the only nonzero rational `2`-torsion point is `(0, 0)` and `t = dim_𝔽₂ E(ℚ)[2] = 1`.

The certificate gives `ρ = 4` points with `𝔽₂`-independent descent images and bounds
`|E(ℚ)[2]| ≤ 2` from the root `R = 0` and the witness prime `ℓ = 5`, at which `x² - 82`
has no root mod `5`. These combine to `rank ≥ ρ - t = 4 - 1 = 3`. Points (short-model
coordinates) are in `data/curve13.txt`, descent labels in `data/curve13-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of ICARM leaderboard curve 13. -/
abbrev curve13A₄ : ℚ := -82

/-- ICARM leaderboard curve 13, `y² = x³ - 82 x` over `ℚ`. -/
def curve13 : WeierstrassCurve ℚ := ⟨0, 0, 0, curve13A₄, 0⟩

/-- ICARM leaderboard curve 13 has Mordell-Weil rank at least `3`, with a single rational
`2`-torsion point. -/
theorem curve13_hasRankGE_3 : HasRankGE curve13 3 := by
  unfold curve13 curve13A₄
  certify_curve oneTorsion root 0 witness 5
    points "data/curve13.txt" labels "data/curve13-labels.txt"

/-- Curve 13 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve13.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of curve 13 is `1728` (it has complex multiplication by `ℤ[i]`). -/
theorem curve13_j : curve13.j = 1728 := j_eq_of_beq _ 1728 (by quickRfl)

end ECCompute
