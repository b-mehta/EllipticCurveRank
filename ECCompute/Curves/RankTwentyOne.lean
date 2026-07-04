/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# The Nagao-Kouya curve has rank at least 21

The Nagao-Kouya elliptic curve

  `E : y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `                  - 19474361277787151947255961435459054151501792241320535`

over `ℚ` has Mordell-Weil rank at least `21`, the 1994 rank record of K. Nagao and T. Kouya. Points
in `data/rank21.txt`, descent labels in `data/rank21-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve ModelIso ModelChange

set_option maxRecDepth 100000

/-- The `a₄` coefficient of the Nagao-Kouya rank-21 curve (general model). -/
abbrev nk21A₄ : ℤ := -215843772422443922015169952702159835

/-- The `a₆` coefficient of the Nagao-Kouya rank-21 curve (general model). -/
abbrev nk21A₆ : ℤ := -19474361277787151947255961435459054151501792241320535

/-- The Nagao-Kouya rank-21 elliptic curve over `ℚ`. Certified rank ≥ 21 in
`nagaoKouya_hasRankGE_21`. -/
def curveNagaoKouya21 : WeierstrassCurve ℚ := toCurveQ 1 1 1 nk21A₄ nk21A₆

/-- The Nagao-Kouya curve has Mordell-Weil rank at least `21`. -/
theorem nagaoKouya_hasRankGE_21 : HasRankGE curveNagaoKouya21 21 := by
  unfold curveNagaoKouya21 nk21A₄ nk21A₆
  certify_curve torsion 11 points "data/rank21.txt" labels "data/rank21-labels.txt"

end ECCompute
