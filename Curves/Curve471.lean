/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 471 has rank at least 14

The elliptic curve recorded as
[curve 471](https://elliptic-rank.icarm.cloud/curve/471) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1074823784146380656`   and
  `a₆ = 428719158724371531410862336`

over `ℚ`. It has Mordell-Weil rank at least `14`. Submitted to the leaderboard by Alexandar Slavov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 471 over `ℚ`. -/
@[expose] public def curve471 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1074823784146380656, 428719158724371531410862336⟩

/-- ICARM leaderboard curve 471 has Mordell-Weil rank at least `14`. -/
public theorem curve471_hasRankGE_14 : HasRankGE curve471 14 := by
  unfold curve471
  certify_curve torsion 29 "data/curve471.txt" "data/curve471-labels.txt"

/-- Curve 471 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve471.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 471. -/
public theorem curve471_j : curve471.j = 137320544393603356387394619402731578644224058416015907303169 / 66257033241903953545157666376524076784274994640281600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
