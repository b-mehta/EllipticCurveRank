/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Martin-McMillen curve has rank at least 23

The Martin-McMillen elliptic curve

  `E : y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `                    + 32685500727716376257923347071452044295907443056345614006`

over `ℚ` has Mordell-Weil rank at least `23`. Points in `data/rank23.txt`, descent labels in
`data/rank23-labels.txt` (primes `7` to `163`, from §2.3 of Cremona's *On the computation of
Mordell-Weil and 2-Selmer groups*); `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

/-- The `a₄` coefficient of the Martin-McMillen curve (general model). -/
abbrev mmA₄ : ℤ := -19252966408674012828065964616418441723

/-- The `a₆` coefficient of the Martin-McMillen curve (general model). -/
abbrev mmA₆ : ℤ := 32685500727716376257923347071452044295907443056345614006

/-- The Martin-McMillen curve over `ℚ`. Certified rank ≥ 23 in `martinMcMillen_hasRankGE_23`. -/
def curveMartinMcMillen : WeierstrassCurve ℚ := toCurveQ 1 0 1 mmA₄ mmA₆

/-- The Martin-McMillen curve has Mordell-Weil rank at least `23`. -/
theorem martinMcMillen_hasRankGE_23 : HasRankGE curveMartinMcMillen 23 := by
  unfold curveMartinMcMillen mmA₄ mmA₆
  certify_curve torsion 29 points "data/rank23.txt" labels "data/rank23-labels.txt"

end ECCompute
