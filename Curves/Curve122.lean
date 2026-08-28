/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 122 has rank at least 7

The elliptic curve recorded as
[curve 122](https://elliptic-rank.icarm.cloud/curve/122) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -92656`   and
  `a₆ = 10865908`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve122.txt`; descent labels are in
`data/curve122-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 122 over `ℚ`. -/
@[expose] public def curve122 : WeierstrassCurve ℚ := ⟨1, -1, 0, -92656, 10865908⟩

/-- ICARM leaderboard curve 122 has Mordell-Weil rank at least `7`. -/
public theorem curve122_hasRankGE_7 : HasRankGE curve122 7 := by
  unfold curve122
  certify_curve torsion 5 "data/curve122.txt" "data/curve122-labels.txt"

/-- Curve 122 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve122.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 122. -/
public theorem curve122_j : curve122.j = 87972511649688832473 / 121896510346684 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
