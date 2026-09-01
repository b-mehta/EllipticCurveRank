/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 5 has rank at least 17

The elliptic curve recorded as
[curve 5](https://elliptic-rank.icarm.cloud/curve/5) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -18478018087690013395692891145`   and
  `a₆ = 966788754934919721471057668405679651084743`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 5 over `ℚ`. -/
@[expose] public def curve005 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -18478018087690013395692891145, 966788754934919721471057668405679651084743⟩

/-- ICARM leaderboard curve 5 has Mordell-Weil rank at least `17`. -/
public theorem curve005_hasRankGE_17 : HasRankGE curve005 17 := by
  unfold curve005
  certify_curve torsion 23 "data/curve005.txt" "data/curve005-labels.txt"

/-- Curve 5 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve005.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 5. -/
public theorem curve005_j : curve005.j = -85172605363286751757810440490167745744331842433210578924192450713759575710337241352928 / 89638681496460857134538595913848649996458570769067216788492587002648982421875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
