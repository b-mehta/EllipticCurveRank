/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 125 has rank at least 7

The elliptic curve recorded as
[curve 125](https://elliptic-rank.icarm.cloud/curve/125) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -5983`   and
  `a₆ = 164022`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve125.txt`; descent labels are in
`data/curve125-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 125 over `ℚ`. -/
@[expose] public def curve125 : WeierstrassCurve ℚ := ⟨1, 0, 1, -5983, 164022⟩

/-- ICARM leaderboard curve 125 has Mordell-Weil rank at least `7`. -/
public theorem curve125_hasRankGE_7 : HasRankGE curve125 7 := by
  unfold curve125
  certify_curve torsion 11 "data/curve125.txt" "data/curve125-labels.txt"

/-- Curve 125 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve125.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 125. -/
public theorem curve125_j : curve125.j = 23679709549154281 / 2010552189452 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
