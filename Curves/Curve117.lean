/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 117 has rank at least 6

The elliptic curve recorded as
[curve 117](https://elliptic-rank.icarm.cloud/curve/117) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -379`   and
  `a₆ = 5172`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve117.txt`; descent labels are in
`data/curve117-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 117 over `ℚ`. -/
@[expose] public def curve117 : WeierstrassCurve ℚ := ⟨0, 0, 1, -379, 5172⟩

/-- ICARM leaderboard curve 117 has Mordell-Weil rank at least `6`. -/
public theorem curve117_hasRankGE_6 : HasRankGE curve117 6 := by
  unfold curve117
  certify_curve torsion 5 "data/curve117.txt" "data/curve117-labels.txt"

/-- Curve 117 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve117.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 117. -/
public theorem curve117_j : curve117.j = -6020621733888 / 8072781371 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
