/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Martin-McMillen curve has rank at least 24

The Martin-McMillen elliptic curve

  `E : y² + xy + y = x³ - 120039822036992245303534619191166796374 x`
  `                  + 504224992484910670010801799168082726759443756222911415116`

over `ℚ` has Mordell-Weil rank at least `24`, the 2000 rank record of R. Martin and W. McMillen.
Points in `data/rank24.txt`, descent labels in `data/rank24-labels.txt`; `certify_curve` does the
rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange


/-- The `a₄` coefficient of the Martin-McMillen rank-24 curve (general model). -/
abbrev mm24A₄ : ℤ := -120039822036992245303534619191166796374

/-- The `a₆` coefficient of the Martin-McMillen rank-24 curve (general model). -/
abbrev mm24A₆ : ℤ := 504224992484910670010801799168082726759443756222911415116

/-- The Martin-McMillen rank-24 elliptic curve over `ℚ`. Certified rank ≥ 24 in
`martinMcMillen_hasRankGE_24`. -/
def curveMartinMcMillen24 : WeierstrassCurve ℚ := toCurveQ 1 0 1 mm24A₄ mm24A₆

/-- The Martin-McMillen curve has Mordell-Weil rank at least `24`. -/
theorem martinMcMillen_hasRankGE_24 : HasRankGE curveMartinMcMillen24 24 := by
  unfold curveMartinMcMillen24 mm24A₄ mm24A₆
  certify_curve torsion 71 points "data/rank24.txt" labels "data/rank24-labels.txt"

end ECCompute
