/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 439 has rank at least 21

The elliptic curve recorded as
[curve 439](https://elliptic-rank.icarm.cloud/curve/439) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -83284362986612591237124770419410460`   and
  `a₆ = 13323832744501378591680462595599415504584388273763600`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 439 over `ℚ`. -/
@[expose] public def curve439 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -83284362986612591237124770419410460,
    13323832744501378591680462595599415504584388273763600⟩

/-- ICARM leaderboard curve 439 has Mordell-Weil rank at least `21`. -/
public theorem curve439_hasRankGE_21 : HasRankGE curve439 21 := by
  unfold curve439
  certify_curve torsion 37 "data/curve439.txt" "data/curve439-labels.txt"

/-- Curve 439 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve439.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 439. -/
public theorem curve439_j : curve439.j = -63887238610694611932898032255968353170696535779900644334688901256366147182132224571967227810712512623662997441 / 39718810606077930167476934805655304641592918506960890175061918369101870306860126560331166758723567360000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
