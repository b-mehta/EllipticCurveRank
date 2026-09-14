/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 52 has rank at least 13

The elliptic curve recorded as
[curve 52](https://elliptic-rank.icarm.cloud/curve/52) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -2827529113871322622866959217`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `13`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 52 over `ℚ`. -/
@[expose] public def curve052 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2827529113871322622866959217, 0⟩

/-- ICARM leaderboard curve 52 has Mordell-Weil rank at least `13`. -/
public theorem curve052_hasRankGE_13 : HasRankGE curve052 13 := by
  unfold curve052
  certify_curve oneTorsion 0 5 "data/curve052.txt" "data/curve052-labels.txt"

/-- Curve 52 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve052.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 52. -/
public theorem curve052_j : curve052.j = 1728 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
