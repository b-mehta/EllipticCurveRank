/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 180 has rank at least 16

The elliptic curve recorded as
[curve 180](https://elliptic-rank.icarm.cloud/curve/180) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -196802191633137450791741`   and
  `a₆ = 32257087916682386944199682931390321`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 180 over `ℚ`. -/
@[expose] public def curve180 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -196802191633137450791741, 32257087916682386944199682931390321⟩

/-- ICARM leaderboard curve 180 has Mordell-Weil rank at least `16`. -/
public theorem curve180_hasRankGE_16 : HasRankGE curve180 16 := by
  unfold curve180
  certify_curve torsion 31 "data/curve180.txt" "data/curve180-labels.txt"

/-- Curve 180 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve180.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 180. -/
public theorem curve180_j : curve180.j = 171580030053285220722588775598135163007710495071296198745588477116021793 / 7801118878730336103423283788352286036165891308796795980262239436800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
