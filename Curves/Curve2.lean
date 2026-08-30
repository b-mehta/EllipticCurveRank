/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 2 has rank at least 2

The elliptic curve recorded as
[curve 2](https://elliptic-rank.icarm.cloud/curve/2) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `2`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 2 over `ℚ`. -/
@[expose] public def curve2 : WeierstrassCurve ℚ := ⟨0, 1, 1, -2, 0⟩

/-- ICARM leaderboard curve 2 has Mordell-Weil rank at least `2`. -/
public theorem curve2_hasRankGE_2 : HasRankGE curve2 2 := by
  unfold curve2
  certify_curve torsion 5 "data/curve2.txt" "data/curve2-labels.txt"

/-- Curve 2 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve2.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 2. -/
public theorem curve2_j : curve2.j = 1404928 / 389 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
