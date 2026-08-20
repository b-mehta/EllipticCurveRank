/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Certify

/-!
# Curve 273 has rank at least 30

The elliptic curve recorded as
[curve 273](https://elliptic-rank.icarm.cloud/curve/273) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -201769035260418549083594900060734240952308696994802735114305555`   and
  `a₆ = 1151107939141058565733479426024323225135665982951300586808823640527729578307`
  `     228357301072889377`

over `ℚ`. It has Mordell-Weil rank at least `30`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve273.txt`; descent labels are in
`data/curve273-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 273 over `ℚ`. -/
def curve273 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -201769035260418549083594900060734240952308696994802735114305555,
    1151107939141058565733479426024323225135665982951300586808823640527729578307228357301072889377⟩

/-- ICARM leaderboard curve 273 has Mordell-Weil rank at least `30`. -/
theorem curve273_hasRankGE_30 : HasRankGE curve273 30 := by
  unfold curve273
  certify_curve torsion 23 points "data/curve273.txt" labels "data/curve273-labels.txt"

end ECCompute
