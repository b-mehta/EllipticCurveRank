/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Check.JInvariant

/-!
# The CM curve y² = x³ - 82x has rank at least 3

The elliptic curve `E : y² = x³ - 82 x` over `ℚ` has Mordell-Weil rank at least `3`.
Its `2`-division cubic factors as `x (x² - 82)`, and `x² - 82` is irreducible over `ℚ`,
so the only nonzero rational `2`-torsion point is `(0, 0)` and `t = dim_𝔽₂ E(ℚ)[2] = 1`.

The certificate gives `ρ = 4` points with `𝔽₂`-independent descent images and bounds
`|E(ℚ)[2]| ≤ 2` from the root `R = 0` and the witness prime `ℓ = 5`, at which `x² - 82`
has no root mod `5`. These combine to `rank ≥ ρ - t = 4 - 1 = 3`. Points (short-model
coordinates) are in `data/cm82.txt`, descent labels in `data/cm82-labels.txt`.
-/

namespace ECCompute

open WeierstrassCurve

/-- The CM curve `y² = x³ - 82 x` over `ℚ`. Certified rank ≥ 3 in `curveCM82_hasRankGE_3`. -/
def curveCM82 : WeierstrassCurve ℚ := ⟨0, 0, 0, -82, 0⟩

/-- The CM curve has Mordell-Weil rank at least `3`, with a single rational
`2`-torsion point. -/
theorem curveCM82_hasRankGE_3 : HasRankGE curveCM82 3 := by
  unfold curveCM82
  certify_curve oneTorsion root 0 witness 5
    points "data/cm82.txt" labels "data/cm82-labels.txt"

/-- The CM curve is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curveCM82.IsElliptic := isElliptic_of_bne (by quickRfl)

/-- The `j`-invariant of the CM curve is `1728` (it has complex multiplication by `ℤ[i]`). -/
theorem curveCM82_j : curveCM82.j = 1728 := j_eq_of_beq _ 1728 (by quickRfl)

end ECCompute
