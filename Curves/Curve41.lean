/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 41 has rank at least 5

The elliptic curve recorded as
[curve 41](https://elliptic-rank.icarm.cloud/curve/41) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -79`   and
  `a₆ = 342`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve41.txt`; descent labels are in
`data/curve41-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 41 over `ℚ`. -/
@[expose] public def curve41 : WeierstrassCurve ℚ := ⟨0, 0, 1, -79, 342⟩

/-- ICARM leaderboard curve 41 has Mordell-Weil rank at least `5`. -/
public theorem curve41_hasRankGE_5 : HasRankGE curve41 5 := by
  unfold curve41
  certify_curve torsion 5 "data/curve41.txt" "data/curve41-labels.txt"

/-- Curve 41 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve41.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 41. -/
public theorem curve41_j : curve41.j = -54526169088 / 19047851 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
