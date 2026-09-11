/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 56 has rank at least 6

The elliptic curve recorded as
[curve 56](https://elliptic-rank.icarm.cloud/curve/56) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -277`   and
  `a₆ = 4566`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 56 over `ℚ`. -/
@[expose] public def curve056 : WeierstrassCurve ℚ := ⟨0, 0, 1, -277, 4566⟩

/-- ICARM leaderboard curve 56 has Mordell-Weil rank at least `6`. -/
public theorem curve056_hasRankGE_6 : HasRankGE curve056 6 := by
  unfold curve056
  certify_curve torsion 17 "data/curve056.txt" "data/curve056-labels.txt"

/-- Curve 56 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve056.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 56. -/
public theorem curve056_j : curve056.j = -2350514958336 / 7647224363 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
