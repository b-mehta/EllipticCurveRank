/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 272 has rank at least 6

The elliptic curve recorded as
[curve 272](https://elliptic-rank.icarm.cloud/curve/272) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 1190790012412`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by sorinmg.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 272 over `ℚ`. -/
@[expose] public def curve272 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1190790012412⟩

/-- ICARM leaderboard curve 272 has Mordell-Weil rank at least `6`. -/
public theorem curve272_hasRankGE_6 : HasRankGE curve272 6 := by
  unfold curve272
  certify_curve torsion 31 "data/curve272.txt" "data/curve272-labels.txt"

/-- Curve 272 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve272.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 272. -/
public theorem curve272_j : curve272.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
