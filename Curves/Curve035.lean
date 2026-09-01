/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 35 has rank at least 14

The elliptic curve recorded as
[curve 35](https://elliptic-rank.icarm.cloud/curve/35) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1692310759026568999140789578145`   and
  `a₆ = 839379398840982294584587970773038145228669599`

over `ℚ`. It has Mordell-Weil rank at least `14`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 35 over `ℚ`. -/
@[expose] public def curve035 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -1692310759026568999140789578145, 839379398840982294584587970773038145228669599⟩

/-- ICARM leaderboard curve 35 has Mordell-Weil rank at least `14`. -/
public theorem curve035_hasRankGE_14 : HasRankGE curve035 14 := by
  unfold curve035
  certify_curve oneTorsion 3239293307633412 5 "data/curve035.txt" "data/curve035-labels.txt"

/-- Curve 35 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve035.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 35. -/
public theorem curve035_j : curve035.j = 483941743120924000812123996730853715578647268051688786879688 / 5250870830712351132421548861849566889806152906127048721 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
