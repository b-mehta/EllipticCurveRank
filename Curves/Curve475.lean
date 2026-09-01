/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 475 has rank at least 12

The elliptic curve recorded as
[curve 475](https://elliptic-rank.icarm.cloud/curve/475) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -113679727`   and
  `a₆ = 682491235476`

over `ℚ`. It has Mordell-Weil rank at least `12`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 475 over `ℚ`. -/
@[expose] public def curve475 : WeierstrassCurve ℚ := ⟨0, 0, 1, -113679727, 682491235476⟩

/-- ICARM leaderboard curve 475 has Mordell-Weil rank at least `12`. -/
public theorem curve475_hasRankGE_12 : HasRankGE curve475 12 := by
  unfold curve475
  certify_curve torsion 7 "data/curve475.txt" "data/curve475-labels.txt"

/-- Curve 475 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve475.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 475. -/
public theorem curve475_j : curve475.j = -162469849448867337195383771136 / 107201228152577318687714363 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
