/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 51 has rank at least 13

The elliptic curve recorded as
[curve 51](https://elliptic-rank.icarm.cloud/curve/51) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 90389647280869401176648335`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `13`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 51 over `ℚ`. -/
@[expose] public def curve51 : WeierstrassCurve ℚ := ⟨0, 0, 0, 90389647280869401176648335, 0⟩

/-- ICARM leaderboard curve 51 has Mordell-Weil rank at least `13`. -/
public theorem curve51_hasRankGE_13 : HasRankGE curve51 13 := by
  unfold curve51
  certify_curve oneTorsion 0 11 "data/curve51.txt" "data/curve51-labels.txt"

/-- Curve 51 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve51.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 51. -/
public theorem curve51_j : curve51.j = 1728 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
