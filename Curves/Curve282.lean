/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 282 has rank at least 20

The elliptic curve recorded as
[curve 282](https://elliptic-rank.icarm.cloud/curve/282) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -724392592785859978141334075420616`   and
  `a₆ = 7118072780333921924205799244128960519106245831620`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve282.txt`; descent labels are in
`data/curve282-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 282 over `ℚ`. -/
@[expose] public def curve282 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -724392592785859978141334075420616, 7118072780333921924205799244128960519106245831620⟩

/-- ICARM leaderboard curve 282 has Mordell-Weil rank at least `20`. -/
public theorem curve282_hasRankGE_20 : HasRankGE curve282 20 := by
  unfold curve282
  certify_curve torsion 17 "data/curve282.txt" "data/curve282-labels.txt"

/-- Curve 282 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve282.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 282. -/
public theorem curve282_j : curve282.j = 41053081173544969584269465886105222910276518783704173948262625831542588253092643454631167373056572196 / 2382446328805378714772428079500289409508353983274485333109053242725752120165935552776762492503925 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
