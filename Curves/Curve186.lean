/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 186 has rank at least 16

The elliptic curve recorded as
[curve 186](https://elliptic-rank.icarm.cloud/curve/186) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -433375986345644467803047`   and
  `a₆ = 107998191356151184499232541284273119`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 186 over `ℚ`. -/
@[expose] public def curve186 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -433375986345644467803047, 107998191356151184499232541284273119⟩

/-- ICARM leaderboard curve 186 has Mordell-Weil rank at least `16`. -/
public theorem curve186_hasRankGE_16 : HasRankGE curve186 16 := by
  unfold curve186
  certify_curve torsion 13 "data/curve186.txt" "data/curve186-labels.txt"

/-- Curve 186 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve186.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 186. -/
public theorem curve186_j : curve186.j = 12347832031628432752954334365847259791791097562142503628310122665708286249 / 233967633902633983979755459859152071254151669331191204489323520000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
