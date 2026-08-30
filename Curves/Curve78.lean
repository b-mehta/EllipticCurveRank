/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 78 has rank at least 8

The elliptic curve recorded as
[curve 78](https://elliptic-rank.icarm.cloud/curve/78) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -201814`   and
  `a₆ = 34925104`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 78 over `ℚ`. -/
@[expose] public def curve78 : WeierstrassCurve ℚ := ⟨1, -1, 0, -201814, 34925104⟩

/-- ICARM leaderboard curve 78 has Mordell-Weil rank at least `8`. -/
public theorem curve78_hasRankGE_8 : HasRankGE curve78 8 := by
  unfold curve78
  certify_curve torsion 13 "data/curve78.txt" "data/curve78-labels.txt"

/-- Curve 78 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve78.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 78. -/
public theorem curve78_j : curve78.j = 909031208520136752441 / 643509175703572 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
