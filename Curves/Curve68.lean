/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 68 has rank at least 15

The elliptic curve recorded as
[curve 68](https://elliptic-rank.icarm.cloud/curve/68) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 46974552981863676115647417`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 68 over `ℚ`. -/
@[expose] public def curve68 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 46974552981863676115647417⟩

/-- ICARM leaderboard curve 68 has Mordell-Weil rank at least `15`. -/
public theorem curve68_hasRankGE_15 : HasRankGE curve68 15 := by
  unfold curve68
  certify_curve torsion 7 "data/curve68.txt" "data/curve68-labels.txt"

/-- Curve 68 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve68.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 68. -/
public theorem curve68_j : curve68.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
