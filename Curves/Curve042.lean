/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 42 has rank at least 1

The elliptic curve recorded as
[curve 42](https://elliptic-rank.icarm.cloud/curve/42) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 42 over `ℚ`. -/
@[expose] public def curve042 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

/-- ICARM leaderboard curve 42 has Mordell-Weil rank at least `1`. -/
public theorem curve042_hasRankGE_1 : HasRankGE curve042 1 := by
  unfold curve042
  certify_curve torsion 7 "data/curve042.txt" "data/curve042-labels.txt"

/-- Curve 42 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve042.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 42. -/
public theorem curve042_j : curve042.j = 110592 / 37 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
