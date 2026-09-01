/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 425 has rank at least 1

The elliptic curve recorded as
[curve 425](https://elliptic-rank.icarm.cloud/curve/425) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 425 over `ℚ`. -/
@[expose] public def curve425 : WeierstrassCurve ℚ := ⟨1, -1, 1, 0, 0⟩

/-- ICARM leaderboard curve 425 has Mordell-Weil rank at least `1`. -/
public theorem curve425_hasRankGE_1 : HasRankGE curve425 1 := by
  unfold curve425
  certify_curve torsion 13 "data/curve425.txt" "data/curve425-labels.txt"

/-- Curve 425 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve425.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 425. -/
public theorem curve425_j : curve425.j = 3375 / 53 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
