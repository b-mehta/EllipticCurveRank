/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 103 has rank at least 14

The elliptic curve recorded as
[curve 103](https://elliptic-rank.icarm.cloud/curve/103) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -277442745099`   and
  `a₆ = 47682424180908449`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve103.txt`; descent labels are in
`data/curve103-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 103 over `ℚ`. -/
@[expose] public def curve103 : WeierstrassCurve ℚ := ⟨1, -1, 0, -277442745099, 47682424180908449⟩

/-- ICARM leaderboard curve 103 has Mordell-Weil rank at least `14`. -/
public theorem curve103_hasRankGE_14 : HasRankGE curve103 14 := by
  unfold curve103
  certify_curve torsion 7 "data/curve103.txt" "data/curve103-labels.txt"

/-- Curve 103 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve103.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 103. -/
public theorem curve103_j : curve103.j = 3239785835820856727883767558604755889 / 527553418721327754704210252631988 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
