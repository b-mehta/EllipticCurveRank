/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 49 has rank at least 10

The elliptic curve recorded as
[curve 49](https://elliptic-rank.icarm.cloud/curve/49) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -16312387`   and
  `a₆ = 25970162646`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 49 over `ℚ`. -/
@[expose] public def curve49 : WeierstrassCurve ℚ := ⟨0, 0, 1, -16312387, 25970162646⟩

/-- ICARM leaderboard curve 49 has Mordell-Weil rank at least `10`. -/
public theorem curve49_hasRankGE_10 : HasRankGE curve49 10 := by
  unfold curve49
  certify_curve torsion 7 "data/curve49.txt" "data/curve49-labels.txt"

/-- Curve 49 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve49.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 49. -/
public theorem curve49_j : curve49.j = -480038710884898894251134976 / 13561938370754827085483 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
