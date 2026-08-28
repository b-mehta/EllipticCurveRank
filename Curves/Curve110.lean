/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 110 has rank at least 5

The elliptic curve recorded as
[curve 110](https://elliptic-rank.icarm.cloud/curve/110) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -100`   and
  `a₆ = 110`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve110.txt`; descent labels are in
`data/curve110-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 110 over `ℚ`. -/
@[expose] public def curve110 : WeierstrassCurve ℚ := ⟨0, 1, 1, -100, 110⟩

/-- ICARM leaderboard curve 110 has Mordell-Weil rank at least `5`. -/
public theorem curve110_hasRankGE_5 : HasRankGE curve110 5 := by
  unfold curve110
  certify_curve torsion 11 "data/curve110.txt" "data/curve110-labels.txt"

/-- Curve 110 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve110.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 110. -/
public theorem curve110_j : curve110.j = 111701610496 / 55726757 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
