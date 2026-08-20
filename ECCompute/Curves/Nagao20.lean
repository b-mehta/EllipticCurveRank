/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# Nagao's curve has rank at least 20

Nagao's elliptic curve

  `E : y² + xy = x³ - 431092980766333677958362095891166 x`
  `              + 5156283555366643659035652799871176909391533088196`

over `ℚ` has Mordell-Weil rank at least `20`, the 1993 rank record of K. Nagao. Points in
`data/nagao20.txt`, descent labels in `data/nagao20-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- Nagao's rank-20 elliptic curve over `ℚ`. Certified rank ≥ 20 in
`curveNagao20_hasRankGE_20`. -/
def curveNagao20 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -431092980766333677958362095891166,
    5156283555366643659035652799871176909391533088196⟩

/-- Nagao's curve has Mordell-Weil rank at least `20`. -/
theorem curveNagao20_hasRankGE_20 : HasRankGE curveNagao20 20 := by
  unfold curveNagao20
  certify_curve torsion 23 points "data/nagao20.txt" labels "data/nagao20-labels.txt"

end ECCompute
