/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 133 has rank at least 9

The elliptic curve recorded as
[curve 133](https://elliptic-rank.icarm.cloud/curve/133) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -3835819`   and
  `a₆ = 2889890730`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 133 over `ℚ`. -/
@[expose] public def curve133 : WeierstrassCurve ℚ := ⟨0, 0, 1, -3835819, 2889890730⟩

/-- ICARM leaderboard curve 133 has Mordell-Weil rank at least `9`. -/
public theorem curve133_hasRankGE_9 : HasRankGE curve133 9 := by
  unfold curve133
  certify_curve torsion 5 "data/curve133.txt" "data/curve133-labels.txt"

/-- Curve 133 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve133.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 133. -/
public theorem curve133_j : curve133.j = 6241630140829494366179328 / 4220116683630718069 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
