/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 43 has rank at least 6

The elliptic curve recorded as
[curve 43](https://elliptic-rank.icarm.cloud/curve/43) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2582`   and
  `a₆ = 48720`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 43 over `ℚ`. -/
@[expose] public def curve043 : WeierstrassCurve ℚ := ⟨1, 1, 0, -2582, 48720⟩

/-- ICARM leaderboard curve 43 has Mordell-Weil rank at least `6`. -/
public theorem curve043_hasRankGE_6 : HasRankGE curve043 6 := by
  unfold curve043
  certify_curve torsion 17 "data/curve043.txt" "data/curve043-labels.txt"

/-- Curve 43 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve043.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 43. -/
public theorem curve043_j : curve043.j = 1904825573752681 / 31125382452 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
