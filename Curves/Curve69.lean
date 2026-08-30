/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 69 has rank at least 2

The elliptic curve recorded as
[curve 69](https://elliptic-rank.icarm.cloud/curve/69) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 1`

over `ℚ`. It has Mordell-Weil rank at least `2`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 69 over `ℚ`. -/
@[expose] public def curve69 : WeierstrassCurve ℚ := ⟨1, 0, 0, 0, 1⟩

/-- ICARM leaderboard curve 69 has Mordell-Weil rank at least `2`. -/
public theorem curve69_hasRankGE_2 : HasRankGE curve69 2 := by
  unfold curve69
  certify_curve torsion 7 "data/curve69.txt" "data/curve69-labels.txt"

/-- Curve 69 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve69.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 69. -/
public theorem curve69_j : curve69.j = -1 / 433 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
