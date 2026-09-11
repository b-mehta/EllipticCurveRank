/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 57 has rank at least 7

The elliptic curve recorded as
[curve 57](https://elliptic-rank.icarm.cloud/curve/57) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1387`   and
  `a₆ = 68046`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 57 over `ℚ`. -/
@[expose] public def curve057 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1387, 68046⟩

/-- ICARM leaderboard curve 57 has Mordell-Weil rank at least `7`. -/
public theorem curve057_hasRankGE_7 : HasRankGE curve057 7 := by
  unfold curve057
  certify_curve torsion 11 "data/curve057.txt" "data/curve057-labels.txt"

/-- Curve 57 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve057.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 57. -/
public theorem curve057_j : curve057.j = -295089050750976 / 1829517077483 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
