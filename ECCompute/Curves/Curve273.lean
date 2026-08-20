/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Check.JInvariant

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

/-- Curve 273 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve273.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 273. -/
theorem curve273_j : curve273.j = -908421207611619966397301371501291919756761922734684482806268125472094471799504840865963593736467876552674219212405145331405042867323019584013417593982615086603074757004166961559271290889612721 / 46714661255308767314567688733841531918983356002159772613256840842851650254036518701100578342601553513579222272710220496887616034526983492843954090554197033638137245037791044053017600000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
