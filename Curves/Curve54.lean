/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 54 has rank at least 4

The elliptic curve recorded as
[curve 54](https://elliptic-rank.icarm.cloud/curve/54) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -79`   and
  `a₆ = 289`

over `ℚ`. It has Mordell-Weil rank at least `4`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 54 over `ℚ`. -/
@[expose] public def curve54 : WeierstrassCurve ℚ := ⟨1, -1, 0, -79, 289⟩

/-- ICARM leaderboard curve 54 has Mordell-Weil rank at least `4`. -/
public theorem curve54_hasRankGE_4 : HasRankGE curve54 4 := by
  unfold curve54
  certify_curve torsion 7 "data/curve54.txt" "data/curve54-labels.txt"

/-- Curve 54 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve54.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 54. -/
public theorem curve54_j : curve54.j = 54915331401 / 468892 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
