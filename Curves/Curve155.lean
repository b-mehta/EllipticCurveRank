/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 155 has rank at least 9

The elliptic curve recorded as
[curve 155](https://elliptic-rank.icarm.cloud/curve/155) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1188709`   and
  `a₆ = 494972209`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve155.txt`; descent labels are in
`data/curve155-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 155 over `ℚ`. -/
@[expose] public def curve155 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1188709, 494972209⟩

/-- ICARM leaderboard curve 155 has Mordell-Weil rank at least `9`. -/
public theorem curve155_hasRankGE_9 : HasRankGE curve155 9 := by
  unfold curve155
  certify_curve torsion 13 "data/curve155.txt" "data/curve155-labels.txt"

/-- Curve 155 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve155.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 155. -/
public theorem curve155_j : curve155.j = 185759301880089515562921 / 1787732808853363732 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
