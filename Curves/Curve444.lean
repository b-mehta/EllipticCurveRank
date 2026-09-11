/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 444 has rank at least 6

The elliptic curve recorded as
[curve 444](https://elliptic-rank.icarm.cloud/curve/444) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -547`   and
  `a₆ = -2934`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by Andrew Sutherland.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 444 over `ℚ`. -/
@[expose] public def curve444 : WeierstrassCurve ℚ := ⟨0, 0, 1, -547, -2934⟩

/-- ICARM leaderboard curve 444 has Mordell-Weil rank at least `6`. -/
public theorem curve444_hasRankGE_6 : HasRankGE curve444 6 := by
  unfold curve444
  certify_curve torsion 11 "data/curve444.txt" "data/curve444-labels.txt"

/-- Curve 444 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve444.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 444. -/
public theorem curve444_j : curve444.j = 18100296585216 / 6756532597 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
