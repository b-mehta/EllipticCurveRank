/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 82 has rank at least 10

The elliptic curve recorded as
[curve 82](https://elliptic-rank.icarm.cloud/curve/82) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1788817`   and
  `a₆ = 843180666`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 82 over `ℚ`. -/
@[expose] public def curve082 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1788817, 843180666⟩

/-- ICARM leaderboard curve 82 has Mordell-Weil rank at least `10`. -/
public theorem curve082_hasRankGE_10 : HasRankGE curve082 10 := by
  unfold curve082
  certify_curve torsion 19 "data/curve082.txt" "data/curve082-labels.txt"

/-- Curve 82 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve082.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 82. -/
public theorem curve082_j : curve082.j = 633025861193355394461696 / 59202439687694448757 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
