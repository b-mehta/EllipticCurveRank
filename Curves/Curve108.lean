/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 108 has rank at least 5

The elliptic curve recorded as
[curve 108](https://elliptic-rank.icarm.cloud/curve/108) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -415`   and
  `a₆ = 3481`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve108.txt`; descent labels are in
`data/curve108-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 108 over `ℚ`. -/
@[expose] public def curve108 : WeierstrassCurve ℚ := ⟨1, -1, 0, -415, 3481⟩

/-- ICARM leaderboard curve 108 has Mordell-Weil rank at least `5`. -/
public theorem curve108_hasRankGE_5 : HasRankGE curve108 5 := by
  unfold curve108
  certify_curve torsion 7 "data/curve108.txt" "data/curve108-labels.txt"

/-- Curve 108 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve108.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 108. -/
public theorem curve108_j : curve108.j = -7915102102089 / 346723100 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
