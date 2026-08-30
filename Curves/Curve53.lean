/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 53 has rank at least 3

The elliptic curve recorded as
[curve 53](https://elliptic-rank.icarm.cloud/curve/53) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -7`   and
  `a₆ = 6`

over `ℚ`. It has Mordell-Weil rank at least `3`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 53 over `ℚ`. -/
@[expose] public def curve53 : WeierstrassCurve ℚ := ⟨0, 0, 1, -7, 6⟩

/-- ICARM leaderboard curve 53 has Mordell-Weil rank at least `3`. -/
public theorem curve53_hasRankGE_3 : HasRankGE curve53 3 := by
  unfold curve53
  certify_curve torsion 19 "data/curve53.txt" "data/curve53-labels.txt"

/-- Curve 53 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve53.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 53. -/
public theorem curve53_j : curve53.j = 37933056 / 5077 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
