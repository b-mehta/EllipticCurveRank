/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 80 has rank at least 9

The elliptic curve recorded as
[curve 80](https://elliptic-rank.icarm.cloud/curve/80) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -402157`   and
  `a₆ = 96291336`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 80 over `ℚ`. -/
@[expose] public def curve80 : WeierstrassCurve ℚ := ⟨0, 0, 1, -402157, 96291336⟩

/-- ICARM leaderboard curve 80 has Mordell-Weil rank at least `9`. -/
public theorem curve80_hasRankGE_9 : HasRankGE curve80 9 := by
  unfold curve80
  certify_curve torsion 7 "data/curve80.txt" "data/curve80-labels.txt"

/-- Curve 80 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve80.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 80. -/
public theorem curve80_j : curve80.j = 7193009097905050054656 / 157107745029925477 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
