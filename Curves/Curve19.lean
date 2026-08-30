/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 19 has rank at least 6

The elliptic curve recorded as
[curve 19](https://elliptic-rank.icarm.cloud/curve/19) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3272444581`   and
  `a₆ = 72023792282806`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 19 over `ℚ`. -/
@[expose] public def curve19 : WeierstrassCurve ℚ := ⟨0, -1, 0, -3272444581, 72023792282806⟩

/-- ICARM leaderboard curve 19 has Mordell-Weil rank at least `6`. -/
public theorem curve19_hasRankGE_6 : HasRankGE curve19 6 := by
  unfold curve19
  certify_curve oneTorsion 134344 31 "data/curve19.txt" "data/curve19-labels.txt"

/-- Curve 19 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve19.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 19. -/
public theorem curve19_j : curve19.j = 35315050222442294737770643456 / 17606837538436654482975 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
