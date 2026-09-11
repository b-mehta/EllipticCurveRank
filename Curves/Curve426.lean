/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 426 has rank at least 4

The elliptic curve recorded as
[curve 426](https://elliptic-rank.icarm.cloud/curve/426) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -72`   and
  `a₆ = 210`

over `ℚ`. It has Mordell-Weil rank at least `4`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 426 over `ℚ`. -/
@[expose] public def curve426 : WeierstrassCurve ℚ := ⟨0, 1, 1, -72, 210⟩

/-- ICARM leaderboard curve 426 has Mordell-Weil rank at least `4`. -/
public theorem curve426_hasRankGE_4 : HasRankGE curve426 4 := by
  unfold curve426
  certify_curve torsion 5 "data/curve426.txt" "data/curve426-labels.txt"

/-- Curve 426 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve426.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 426. -/
public theorem curve426_j : curve426.j = 41854210048 / 501029 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
