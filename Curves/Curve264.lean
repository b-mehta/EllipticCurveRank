/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 264 has rank at least 8

The elliptic curve recorded as
[curve 264](https://elliptic-rank.icarm.cloud/curve/264) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -7179721`   and
  `a₆ = 11215801`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve264.txt`; descent labels are in
`data/curve264-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 264 over `ℚ`. -/
@[expose] public def curve264 : WeierstrassCurve ℚ := ⟨0, 0, 0, -7179721, 11215801⟩

/-- ICARM leaderboard curve 264 has Mordell-Weil rank at least `8`. -/
public theorem curve264_hasRankGE_8 : HasRankGE curve264 8 := by
  unfold curve264
  certify_curve torsion 13 "data/curve264.txt" "data/curve264-labels.txt"

/-- Curve 264 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve264.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 264. -/
public theorem curve264_j : curve264.j = 2558152518805141095359232 / 1480408940828307756217 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
