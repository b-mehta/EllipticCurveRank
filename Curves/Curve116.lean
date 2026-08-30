/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 116 has rank at least 6

The elliptic curve recorded as
[curve 116](https://elliptic-rank.icarm.cloud/curve/116) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -9227`   and
  `a₆ = 340354`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 116 over `ℚ`. -/
@[expose] public def curve116 : WeierstrassCurve ℚ := ⟨1, 0, 0, -9227, 340354⟩

/-- ICARM leaderboard curve 116 has Mordell-Weil rank at least `6`. -/
public theorem curve116_hasRankGE_6 : HasRankGE curve116 6 := by
  unfold curve116
  certify_curve torsion 5 "data/curve116.txt" "data/curve116-labels.txt"

/-- Curve 116 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve116.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 116. -/
public theorem curve116_j : curve116.j = 86877680157268273 / 6822208199 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
