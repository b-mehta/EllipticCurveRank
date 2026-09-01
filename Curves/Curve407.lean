/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 407 has rank at least 18

The elliptic curve recorded as
[curve 407](https://elliptic-rank.icarm.cloud/curve/407) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -3709951130930525095023568`   and
  `a₆ = 2771978727946269955724382333144546458`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 407 over `ℚ`. -/
@[expose] public def curve407 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -3709951130930525095023568, 2771978727946269955724382333144546458⟩

/-- ICARM leaderboard curve 407 has Mordell-Weil rank at least `18`. -/
public theorem curve407_hasRankGE_18 : HasRankGE curve407 18 := by
  unfold curve407
  certify_curve torsion 17 "data/curve407.txt" "data/curve407-labels.txt"

/-- Curve 407 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve407.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 407. -/
public theorem curve407_j : curve407.j = -5647136415654619899511426225208216954827649202183449041296462294916829565830521 / 51411382397974155997137496716460022041538318345893415134584180167571187500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
