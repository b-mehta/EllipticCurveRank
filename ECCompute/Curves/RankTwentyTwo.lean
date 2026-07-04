/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Fermigier's curve has rank at least 22

Fermigier's elliptic curve

  `E : y² + xy + y = x³ - 940299517776391362903023121165864 x`
  `                  + 10707363070719743033425295515449274534651125011362`

over `ℚ` has Mordell-Weil rank at least `22`, the 1997 rank record of S. Fermigier. Points in
`data/rank22.txt`, descent labels in `data/rank22-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of Fermigier's rank-22 curve (general model). -/
abbrev fermigier22A₄ : ℤ := -940299517776391362903023121165864

/-- The `a₆` coefficient of Fermigier's rank-22 curve (general model). -/
abbrev fermigier22A₆ : ℤ := 10707363070719743033425295515449274534651125011362

/-- Fermigier's rank-22 elliptic curve over `ℚ`. Certified rank ≥ 22 in `fermigier_hasRankGE_22`. -/
def curveFermigier22 : WeierstrassCurve ℚ := toCurveQ 1 0 1 fermigier22A₄ fermigier22A₆

/-- Fermigier's curve has Mordell-Weil rank at least `22`. -/
theorem fermigier_hasRankGE_22 : HasRankGE curveFermigier22 22 := by
  unfold curveFermigier22 fermigier22A₄ fermigier22A₆
  certify_curve torsion 31 points "data/rank22.txt" labels "data/rank22-labels.txt"

end ECCompute
