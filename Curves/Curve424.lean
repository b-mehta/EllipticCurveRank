/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 424 has rank at least 1

The elliptic curve recorded as
[curve 424](https://elliptic-rank.icarm.cloud/curve/424) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 424 over `ℚ`. -/
@[expose] public def curve424 : WeierstrassCurve ℚ := ⟨0, 1, 1, 0, 0⟩

/-- ICARM leaderboard curve 424 has Mordell-Weil rank at least `1`. -/
public theorem curve424_hasRankGE_1 : HasRankGE curve424 1 := by
  unfold curve424
  certify_curve torsion 11 "data/curve424.txt" "data/curve424-labels.txt"

/-- Curve 424 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve424.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 424. -/
public theorem curve424_j : curve424.j = -4096 / 43 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
