/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 107 has rank at least 5

The elliptic curve recorded as
[curve 107](https://elliptic-rank.icarm.cloud/curve/107) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -247`   and
  `a₆ = 1476`

over `ℚ`. It has Mordell-Weil rank at least `5`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 107 over `ℚ`. -/
@[expose] public def curve107 : WeierstrassCurve ℚ := ⟨0, 0, 1, -247, 1476⟩

/-- ICARM leaderboard curve 107 has Mordell-Weil rank at least `5`. -/
public theorem curve107_hasRankGE_5 : HasRankGE curve107 5 := by
  unfold curve107
  certify_curve torsion 11 "data/curve107.txt" "data/curve107-labels.txt"

/-- Curve 107 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve107.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 107. -/
public theorem curve107_j : curve107.j = 1666535510016 / 22966597 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
