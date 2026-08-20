/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve

/-!
# The Nagao-Kouya curve has rank at least 21

The Nagao-Kouya elliptic curve

  `E : y² + xy + y = x³ + x² - 215843772422443922015169952702159835 x`
  `                  - 19474361277787151947255961435459054151501792241320535`

over `ℚ` has Mordell-Weil rank at least `21`, the 1994 rank record of K. Nagao and T. Kouya. Points
in `data/nagaoKouya21.txt`, descent labels in `data/nagaoKouya21-labels.txt`; `certify_curve` does
the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- The Nagao-Kouya rank-21 elliptic curve over `ℚ`. Certified rank ≥ 21 in
`curveNagaoKouya21_hasRankGE_21`. -/
def curveNagaoKouya21 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -215843772422443922015169952702159835,
    -19474361277787151947255961435459054151501792241320535⟩

/-- The Nagao-Kouya curve has Mordell-Weil rank at least `21`. -/
theorem curveNagaoKouya21_hasRankGE_21 : HasRankGE curveNagaoKouya21 21 := by
  unfold curveNagaoKouya21
  certify_curve torsion 11 points "data/nagaoKouya21.txt" labels "data/nagaoKouya21-labels.txt"

end ECCompute
