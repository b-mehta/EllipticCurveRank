/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 113 has rank at least 6

The elliptic curve recorded as
[curve 113](https://elliptic-rank.icarm.cloud/curve/113) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2326`   and
  `a₆ = 43456`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 113 over `ℚ`. -/
@[expose] public def curve113 : WeierstrassCurve ℚ := ⟨1, -1, 0, -2326, 43456⟩

/-- ICARM leaderboard curve 113 has Mordell-Weil rank at least `6`. -/
public theorem curve113_hasRankGE_6 : HasRankGE curve113 6 := by
  unfold curve113
  certify_curve torsion 5 "data/curve113.txt" "data/curve113-labels.txt"

/-- Curve 113 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve113.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 113. -/
public theorem curve113_j : curve113.j = 1392059713710393 / 11479041604 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
