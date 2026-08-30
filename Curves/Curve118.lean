/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 118 has rank at least 6

The elliptic curve recorded as
[curve 118](https://elliptic-rank.icarm.cloud/curve/118) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -889`   and
  `a₆ = 9150`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 118 over `ℚ`. -/
@[expose] public def curve118 : WeierstrassCurve ℚ := ⟨0, 0, 1, -889, 9150⟩

/-- ICARM leaderboard curve 118 has Mordell-Weil rank at least `6`. -/
public theorem curve118_hasRankGE_6 : HasRankGE curve118 6 := by
  unfold curve118
  certify_curve torsion 5 "data/curve118.txt" "data/curve118-labels.txt"

/-- Curve 118 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve118.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 118. -/
public theorem curve118_j : curve118.j = 77701427048448 / 8796007189 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
