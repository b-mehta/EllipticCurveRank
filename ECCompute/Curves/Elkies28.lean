/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# Elkies' curve has rank at least 28

Elkies' elliptic curve

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -20067762415575526585033208209338542750930230312178956502`   and
  `a₆ = 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`

over `ℚ` has Mordell-Weil rank at least `28`, the 2006 rank record of N. D. Elkies. Points in
`data/elkies28.txt`, descent labels in `data/elkies28-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- Elkies' rank-28 elliptic curve over `ℚ`. Certified rank ≥ 28 in
`curveElkies28_hasRankGE_28`. -/
def curveElkies28 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -20067762415575526585033208209338542750930230312178956502,
    34481611795030556467032985690390720374855944359319180361266008296291939448732243429⟩

/-- Elkies' curve has Mordell-Weil rank at least `28`. -/
theorem curveElkies28_hasRankGE_28 : HasRankGE curveElkies28 28 := by
  unfold curveElkies28
  certify_curve torsion 23 points "data/elkies28.txt" labels "data/elkies28-labels.txt"

end ECCompute
