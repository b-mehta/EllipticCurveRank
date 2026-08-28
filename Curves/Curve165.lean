/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 165 has rank at least 17

The elliptic curve recorded as
[curve 165](https://elliptic-rank.icarm.cloud/curve/165) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -27169953542094477689663390`   and
  `a₆ = 54214482321365567882254868382411020852`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve165.txt`; descent labels are in
`data/curve165-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 165 over `ℚ`. -/
@[expose] public def curve165 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -27169953542094477689663390, 54214482321365567882254868382411020852⟩

/-- ICARM leaderboard curve 165 has Mordell-Weil rank at least `17`. -/
public theorem curve165_hasRankGE_17 : HasRankGE curve165 17 := by
  unfold curve165
  certify_curve torsion 5 "data/curve165.txt" "data/curve165-labels.txt"

/-- Curve 165 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve165.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 165. -/
public theorem curve165_j : curve165.j = 2218147385380717012420693025055136574543628231681042806300145173942208289197142873 / 13911346942980486161686871517934679432553631814179561190438456955749228983884 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
