/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 83 has rank at least 10

The elliptic curve recorded as
[curve 83](https://elliptic-rank.icarm.cloud/curve/83) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1856500`   and
  `a₆ = 1072474760`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve83.txt`; descent labels are in
`data/curve83-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 83 over `ℚ`. -/
@[expose] public def curve83 : WeierstrassCurve ℚ := ⟨0, 1, 1, -1856500, 1072474760⟩

/-- ICARM leaderboard curve 83 has Mordell-Weil rank at least `10`. -/
public theorem curve83_hasRankGE_10 : HasRankGE curve83 10 := by
  unfold curve83
  certify_curve torsion 7 "data/curve83.txt" "data/curve83-labels.txt"

/-- Curve 83 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve83.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 83. -/
public theorem curve83_j : curve83.j = -707634187818526550020096 / 87950374485438204043 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
