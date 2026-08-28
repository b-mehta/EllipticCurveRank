/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 135 has rank at least 9

The elliptic curve recorded as
[curve 135](https://elliptic-rank.icarm.cloud/curve/135) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1076185`   and
  `a₆ = 496031340`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve135.txt`; descent labels are in
`data/curve135-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 135 over `ℚ`. -/
@[expose] public def curve135 : WeierstrassCurve ℚ := ⟨1, 0, 1, -1076185, 496031340⟩

/-- ICARM leaderboard curve 135 has Mordell-Weil rank at least `9`. -/
public theorem curve135_hasRankGE_9 : HasRankGE curve135 9 := by
  unfold curve135
  certify_curve torsion 5 "data/curve135.txt" "data/curve135-labels.txt"

/-- Curve 135 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve135.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 135. -/
public theorem curve135_j : curve135.j = -137842752130378578054793 / 26560670518137118576 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
