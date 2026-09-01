/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 450 has rank at least 20

The elliptic curve recorded as
[curve 450](https://elliptic-rank.icarm.cloud/curve/450) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2010468055035388719404423460545238`   and
  `a₆ = 23314207811821692898503348621971264563108905459492`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 450 over `ℚ`. -/
@[expose] public def curve450 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2010468055035388719404423460545238, 23314207811821692898503348621971264563108905459492⟩

/-- ICARM leaderboard curve 450 has Mordell-Weil rank at least `20`. -/
public theorem curve450_hasRankGE_20 : HasRankGE curve450 20 := by
  unfold curve450
  certify_curve torsion 31 "data/curve450.txt" "data/curve450-labels.txt"

/-- Curve 450 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve450.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 450. -/
public theorem curve450_j : curve450.j = 5138352345589965811190825911046902041694918952638694917623773701342255932668964451501560090511825 / 1631023508137834318478546180465511805422333259202002327206952103580097231698773755476507230208 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
