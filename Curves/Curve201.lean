/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 201 has rank at least 13

The elliptic curve recorded as
[curve 201](https://elliptic-rank.icarm.cloud/curve/201) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2033019015003100703`   and
  `a₆ = 1111839781374124406036388487`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 201 over `ℚ`. -/
@[expose] public def curve201 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -2033019015003100703, 1111839781374124406036388487⟩

/-- ICARM leaderboard curve 201 has Mordell-Weil rank at least `13`. -/
public theorem curve201_hasRankGE_13 : HasRankGE curve201 13 := by
  unfold curve201
  certify_curve torsion 47 "data/curve201.txt" "data/curve201-labels.txt"

/-- Curve 201 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve201.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 201. -/
public theorem curve201_j : curve201.j = 1274736747907705489975155260290807210574377698904165302441 / 5139204185335463343589156191762735592574816045363200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
