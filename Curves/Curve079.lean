/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 79 has rank at least 9

The elliptic curve recorded as
[curve 79](https://elliptic-rank.icarm.cloud/curve/79) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -514507`   and
  `a₆ = 140806716`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 79 over `ℚ`. -/
@[expose] public def curve079 : WeierstrassCurve ℚ := ⟨0, 0, 1, -514507, 140806716⟩

/-- ICARM leaderboard curve 79 has Mordell-Weil rank at least `9`. -/
public theorem curve079_hasRankGE_9 : HasRankGE curve079 9 := by
  unfold curve079
  certify_curve torsion 7 "data/curve079.txt" "data/curve079-labels.txt"

/-- Curve 79 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve079.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 79. -/
public theorem curve079_j : curve079.j = 15062517885455604781056 / 151673348057775877 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
