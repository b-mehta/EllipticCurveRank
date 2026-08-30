/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 298 has rank at least 1

The elliptic curve recorded as
[curve 298](https://elliptic-rank.icarm.cloud/curve/298) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 1000000000014000000000048`

over `ℚ`. It has Mordell-Weil rank at least `1`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 298 over `ℚ`. -/
@[expose] public def curve298 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1000000000014000000000048⟩

/-- ICARM leaderboard curve 298 has Mordell-Weil rank at least `1`. -/
public theorem curve298_hasRankGE_1 : HasRankGE curve298 1 := by
  unfold curve298
  certify_curve torsion 13 "data/curve298.txt" "data/curve298-labels.txt"

/-- Curve 298 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve298.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 298. -/
public theorem curve298_j : curve298.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
