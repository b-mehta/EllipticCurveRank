/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 46 has rank at least 16

The elliptic curve recorded as
[curve 46](https://elliptic-rank.icarm.cloud/curve/46) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = -489468383913472842641289697078`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 46 over `ℚ`. -/
@[expose] public def curve46 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, -489468383913472842641289697078⟩

/-- ICARM leaderboard curve 46 has Mordell-Weil rank at least `16`. -/
public theorem curve46_hasRankGE_16 : HasRankGE curve46 16 := by
  unfold curve46
  certify_curve torsion 7 "data/curve46.txt" "data/curve46-labels.txt"

/-- Curve 46 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve46.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 46. -/
public theorem curve46_j : curve46.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
