/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 109 has rank at least 5

The elliptic curve recorded as
[curve 109](https://elliptic-rank.icarm.cloud/curve/109) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -532`   and
  `a₆ = 4420`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve109.txt`; descent labels are in
`data/curve109-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 109 over `ℚ`. -/
@[expose] public def curve109 : WeierstrassCurve ℚ := ⟨0, 0, 0, -532, 4420⟩

/-- ICARM leaderboard curve 109 has Mordell-Weil rank at least `5`. -/
public theorem curve109_hasRankGE_5 : HasRankGE curve109 5 := by
  unfold curve109
  certify_curve torsion 7 "data/curve109.txt" "data/curve109-labels.txt"

/-- Curve 109 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve109.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 109. -/
public theorem curve109_j : curve109.j = 65045707776 / 4674517 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
