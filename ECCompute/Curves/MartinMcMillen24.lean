/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# The Martin-McMillen curve has rank at least 24

The Martin-McMillen elliptic curve

  `E : y² + xy + y = x³ - 120039822036992245303534619191166796374 x`
  `                  + 504224992484910670010801799168082726759443756222911415116`

over `ℚ` has Mordell-Weil rank at least `24`, the 2000 rank record of R. Martin and W. McMillen.
Points in `data/martinMcMillen24.txt`, descent labels in `data/martinMcMillen24-labels.txt`;
`certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The Martin-McMillen rank-24 elliptic curve over `ℚ`. Certified rank ≥ 24 in
`curveMartinMcMillen24_hasRankGE_24`. -/
def curveMartinMcMillen24 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -120039822036992245303534619191166796374,
    504224992484910670010801799168082726759443756222911415116⟩

/-- The Martin-McMillen curve has Mordell-Weil rank at least `24`. -/
theorem curveMartinMcMillen24_hasRankGE_24 : HasRankGE curveMartinMcMillen24 24 := by
  unfold curveMartinMcMillen24
  certify_curve torsion 71 points "data/martinMcMillen24.txt"
    labels "data/martinMcMillen24-labels.txt"

end ECCompute
