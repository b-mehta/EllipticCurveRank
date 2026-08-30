/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 70 has rank at least 3

The elliptic curve recorded as
[curve 70](https://elliptic-rank.icarm.cloud/curve/70) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -6`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `3`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 70 over `ℚ`. -/
@[expose] public def curve70 : WeierstrassCurve ℚ := ⟨1, -1, 1, -6, 0⟩

/-- ICARM leaderboard curve 70 has Mordell-Weil rank at least `3`. -/
public theorem curve70_hasRankGE_3 : HasRankGE curve70 3 := by
  unfold curve70
  certify_curve torsion 7 "data/curve70.txt" "data/curve70-labels.txt"

/-- Curve 70 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve70.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 70. -/
public theorem curve70_j : curve70.j = 20346417 / 11197 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
