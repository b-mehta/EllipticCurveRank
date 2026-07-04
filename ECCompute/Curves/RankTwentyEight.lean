/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Elkies' curve has rank at least 28

Elkies' elliptic curve

  `E : y² + xy + y = x³ - x² - 20067762415575526585033208209338542750930230312178956502 x`
  `                  + 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`

over `ℚ` has Mordell-Weil rank at least `28`, the 2006 rank record of N. D. Elkies. Points in
`data/rank28.txt`, descent labels in `data/rank28-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of Elkies' rank-28 curve (general model). -/
abbrev elkies28A₄ : ℤ := -20067762415575526585033208209338542750930230312178956502

/-- The `a₆` coefficient of Elkies' rank-28 curve (general model). -/
abbrev elkies28A₆ : ℤ :=
  34481611795030556467032985690390720374855944359319180361266008296291939448732243429

/-- Elkies' rank-28 elliptic curve over `ℚ`. Certified rank ≥ 28 in `elkies_hasRankGE_28`. -/
def curveElkies28 : WeierstrassCurve ℚ := toCurveQ 1 (-1) 1 elkies28A₄ elkies28A₆

/-- Elkies' curve has Mordell-Weil rank at least `28`. -/
theorem elkies_hasRankGE_28 : HasRankGE curveElkies28 28 := by
  unfold curveElkies28 elkies28A₄ elkies28A₆
  certify_curve torsion 23 points "data/rank28.txt" labels "data/rank28-labels.txt"

end ECCompute
