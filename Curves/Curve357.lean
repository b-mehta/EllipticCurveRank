/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 357 has rank at least 8

The elliptic curve recorded as
[curve 357](https://elliptic-rank.icarm.cloud/curve/357) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1285029`   and
  `a₆ = 500060929`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve357.txt`; descent labels are in
`data/curve357-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 357 over `ℚ`. -/
@[expose] public def curve357 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1285029, 500060929⟩

/-- ICARM leaderboard curve 357 has Mordell-Weil rank at least `8`. -/
public theorem curve357_hasRankGE_8 : HasRankGE curve357 8 := by
  unfold curve357
  certify_curve torsion 11 "data/curve357.txt" "data/curve357-labels.txt"

/-- Curve 357 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve357.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 357. -/
public theorem curve357_j : curve357.j = 321910513007608569169 / 38296886441142948 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
