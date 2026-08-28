/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 37 has rank at least 17

The elliptic curve recorded as
[curve 37](https://elliptic-rank.icarm.cloud/curve/37) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -957089489055751752507625259831765957846101`   and
  `a₆ = 351598252970651757672333752869879740192822872602430248013582348`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve37.txt`; descent labels are in
`data/curve37-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 37 over `ℚ`. -/
@[expose] public def curve37 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -957089489055751752507625259831765957846101,
    351598252970651757672333752869879740192822872602430248013582348⟩

/-- ICARM leaderboard curve 37 has Mordell-Weil rank at least `17`. -/
public theorem curve37_hasRankGE_17 : HasRankGE curve37 17 := by
  unfold curve37
  certify_curve oneTorsion 2541668599439235342183 11 "data/curve37.txt" "data/curve37-labels.txt"

/-- Curve 37 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve37.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 37. -/
public theorem curve37_j : curve37.j = 85582389105295750433890791399307879674908471750796150868311447255734832505836629920681097333407084610993694071603 / 2387861591204313461913392370028820267438853421409708097753317658480315425364315663374516541615251472828101676 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
