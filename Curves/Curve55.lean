/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 55 has rank at least 5

The elliptic curve recorded as
[curve 55](https://elliptic-rank.icarm.cloud/curve/55) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -22`   and
  `a₆ = 219`

over `ℚ`. It has Mordell-Weil rank at least `5`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 55 over `ℚ`. -/
@[expose] public def curve55 : WeierstrassCurve ℚ := ⟨1, 0, 0, -22, 219⟩

/-- ICARM leaderboard curve 55 has Mordell-Weil rank at least `5`. -/
public theorem curve55_hasRankGE_5 : HasRankGE curve55 5 := by
  unfold curve55
  certify_curve torsion 5 "data/curve55.txt" "data/curve55-labels.txt"

/-- Curve 55 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve55.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 55. -/
public theorem curve55_j : curve55.j = -1180932193 / 20384311 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
