/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 84 has rank at least 10

The elliptic curve recorded as
[curve 84](https://elliptic-rank.icarm.cloud/curve/84) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -2438527`   and
  `a₆ = 1545098346`

over `ℚ`. It has Mordell-Weil rank at least `10`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 84 over `ℚ`. -/
@[expose] public def curve84 : WeierstrassCurve ℚ := ⟨0, 0, 1, -2438527, 1545098346⟩

/-- ICARM leaderboard curve 84 has Mordell-Weil rank at least `10`. -/
public theorem curve84_hasRankGE_10 : HasRankGE curve84 10 := by
  unfold curve84
  certify_curve torsion 7 "data/curve84.txt" "data/curve84-labels.txt"

/-- Curve 84 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve84.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 84. -/
public theorem curve84_j : curve84.j = -1603638291915355209486336 / 103294665688000244363 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
