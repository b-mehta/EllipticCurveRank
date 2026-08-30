/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 106 has rank at least 13

The elliptic curve recorded as
[curve 106](https://elliptic-rank.icarm.cloud/curve/106) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -77547091492`   and
  `a₆ = 6455011172238820`

over `ℚ`. It has Mordell-Weil rank at least `13`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 106 over `ℚ`. -/
@[expose] public def curve106 : WeierstrassCurve ℚ := ⟨0, 0, 0, -77547091492, 6455011172238820⟩

/-- ICARM leaderboard curve 106 has Mordell-Weil rank at least `13`. -/
public theorem curve106_hasRankGE_13 : HasRankGE curve106 13 := by
  unfold curve106
  certify_curve torsion 13 "data/curve106.txt" "data/curve106-labels.txt"

/-- Curve 106 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve106.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 106. -/
public theorem curve106_j : curve106.j = 201456037664600846237528392469154816 / 46270007048061366682219989092197 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
