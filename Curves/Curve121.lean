/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 121 has rank at least 7

The elliptic curve recorded as
[curve 121](https://elliptic-rank.icarm.cloud/curve/121) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -36673`   and
  `a₆ = 2704878`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 121 over `ℚ`. -/
@[expose] public def curve121 : WeierstrassCurve ℚ := ⟨0, 0, 1, -36673, 2704878⟩

/-- ICARM leaderboard curve 121 has Mordell-Weil rank at least `7`. -/
public theorem curve121_hasRankGE_7 : HasRankGE curve121 7 := by
  unfold curve121
  certify_curve torsion 7 "data/curve121.txt" "data/curve121-labels.txt"

/-- Curve 121 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve121.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 121. -/
public theorem curve121_j : curve121.j = -5454601499184574464 / 4072172237675 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
