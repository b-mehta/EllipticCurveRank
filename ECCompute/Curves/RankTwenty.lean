/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Nagao's curve has rank at least 20

Nagao's elliptic curve

  `E : y² + xy = x³ - 431092980766333677958362095891166 x`
  `              + 5156283555366643659035652799871176909391533088196`

over `ℚ` has Mordell-Weil rank at least `20`, the 1993 rank record of K. Nagao. Points in
`data/rank20.txt`, descent labels in `data/rank20-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The `a₄` coefficient of Nagao's rank-20 curve (general model). -/
abbrev nagao20A₄ : ℚ := -431092980766333677958362095891166

/-- The `a₆` coefficient of Nagao's rank-20 curve (general model). -/
abbrev nagao20A₆ : ℚ := 5156283555366643659035652799871176909391533088196

/-- Nagao's rank-20 elliptic curve over `ℚ`. Certified rank ≥ 20 in `nagao_hasRankGE_20`. -/
def curveNagao20 : WeierstrassCurve ℚ := ⟨1, 0, 0, nagao20A₄, nagao20A₆⟩

/-- Nagao's curve has Mordell-Weil rank at least `20`. -/
theorem nagao_hasRankGE_20 : HasRankGE curveNagao20 20 := by
  unfold curveNagao20 nagao20A₄ nagao20A₆
  certify_curve torsion 23 points "data/rank20.txt" labels "data/rank20-labels.txt"

end ECCompute
