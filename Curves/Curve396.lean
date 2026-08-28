/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 396 has rank at least 25

The elliptic curve recorded as
[curve 396](https://elliptic-rank.icarm.cloud/curve/396) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -61892122170276517714464524289071240329708`   and
  `a₆ = 1412172132176588711941495717130133429244688284956311756421488`

over `ℚ`. It has Mordell-Weil rank at least `25`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve396.txt`; descent labels are in
`data/curve396-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 396 over `ℚ`. -/
@[expose] public def curve396 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -61892122170276517714464524289071240329708,
    1412172132176588711941495717130133429244688284956311756421488⟩

/-- ICARM leaderboard curve 396 has Mordell-Weil rank at least `25`. -/
public theorem curve396_hasRankGE_25 : HasRankGE curve396 25 := by
  unfold curve396
  certify_curve torsion 23 "data/curve396.txt" "data/curve396-labels.txt"

/-- Curve 396 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve396.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 396. -/
public theorem curve396_j : curve396.j = 163873923524801334177973577271971715667775865801638367311143954161660956656705261267824186061735828187385859981865874850000 / 89450025130840364955672846809759113802730344189962269382602213793054820415721894016012149137316118085266480480915902053 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
