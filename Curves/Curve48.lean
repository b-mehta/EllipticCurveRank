/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 48 has rank at least 9

The elliptic curve recorded as
[curve 48](https://elliptic-rank.icarm.cloud/curve/48) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -135004`   and
  `a₆ = 97151644`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve48.txt`; descent labels are in
`data/curve48-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 48 over `ℚ`. -/
@[expose] public def curve48 : WeierstrassCurve ℚ := ⟨1, -1, 0, -135004, 97151644⟩

/-- ICARM leaderboard curve 48 has Mordell-Weil rank at least `9`. -/
public theorem curve48_hasRankGE_9 : HasRankGE curve48 9 := by
  unfold curve48
  certify_curve torsion 7 "data/curve48.txt" "data/curve48-labels.txt"

/-- Curve 48 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve48.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 48. -/
public theorem curve48_j : curve48.j = -272123112996603560601 / 3917095724831382908 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
