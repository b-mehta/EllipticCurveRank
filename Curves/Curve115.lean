/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 115 has rank at least 6

The elliptic curve recorded as
[curve 115](https://elliptic-rank.icarm.cloud/curve/115) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -63147`   and
  `a₆ = 6081915`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve115.txt`; descent labels are in
`data/curve115-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 115 over `ℚ`. -/
@[expose] public def curve115 : WeierstrassCurve ℚ := ⟨1, -1, 1, -63147, 6081915⟩

/-- ICARM leaderboard curve 115 has Mordell-Weil rank at least `6`. -/
public theorem curve115_hasRankGE_6 : HasRankGE curve115 6 := by
  unfold curve115
  certify_curve torsion 13 "data/curve115.txt" "data/curve115-labels.txt"

/-- Curve 115 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve115.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 115. -/
public theorem curve115_j : curve115.j = 27846808802488401921 / 218351628255232 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
