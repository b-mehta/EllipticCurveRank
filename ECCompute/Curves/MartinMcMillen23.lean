/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# The Martin-McMillen curve has rank at least 23

The Martin-McMillen elliptic curve

  `E : y² + xy + y = x³ - 19252966408674012828065964616418441723 x`
  `                    + 32685500727716376257923347071452044295907443056345614006`

over `ℚ` has Mordell-Weil rank at least `23`. Points in `data/martinMcMillen23.txt`, descent labels
in `data/martinMcMillen23-labels.txt` (primes `7` to `163`, from §2.3 of Cremona's *On the
computation of Mordell-Weil and 2-Selmer groups*); `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The Martin-McMillen curve over `ℚ`. Certified rank ≥ 23 in
`curveMartinMcMillen23_hasRankGE_23`. -/
def curveMartinMcMillen23 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -19252966408674012828065964616418441723,
    32685500727716376257923347071452044295907443056345614006⟩

/-- The Martin-McMillen curve has Mordell-Weil rank at least `23`. -/
theorem curveMartinMcMillen23_hasRankGE_23 : HasRankGE curveMartinMcMillen23 23 := by
  unfold curveMartinMcMillen23
  certify_curve torsion 29 points "data/martinMcMillen23.txt"
    labels "data/martinMcMillen23-labels.txt"

end ECCompute
