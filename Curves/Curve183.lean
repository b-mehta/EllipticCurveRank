/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 183 has rank at least 16

The elliptic curve recorded as
[curve 183](https://elliptic-rank.icarm.cloud/curve/183) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -323202197541587323322357413`   and
  `a₆ = 2206561434845879634664264564474894007531`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve183.txt`; descent labels are in
`data/curve183-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 183 over `ℚ`. -/
@[expose] public def curve183 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -323202197541587323322357413, 2206561434845879634664264564474894007531⟩

/-- ICARM leaderboard curve 183 has Mordell-Weil rank at least `16`. -/
public theorem curve183_hasRankGE_16 : HasRankGE curve183 16 := by
  unfold curve183
  certify_curve torsion 41 "data/curve183.txt" "data/curve183-labels.txt"

/-- Curve 183 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve183.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 183. -/
public theorem curve183_j : curve183.j = 238960765650829107155755627406184990433150664887526935190852448222928577077491337 / 3671763385759840282412921471427718253413383874597913804378295692444230754304 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
