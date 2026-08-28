/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 304 has rank at least 22

The elliptic curve recorded as
[curve 304](https://elliptic-rank.icarm.cloud/curve/304) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1998675662524543869448537818094316`   and
  `a₆ = 34278416330918655840201783804131603181718906590096`

over `ℚ`. It has Mordell-Weil rank at least `22`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve304.txt`; descent labels are in
`data/curve304-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 304 over `ℚ`. -/
@[expose] public def curve304 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1998675662524543869448537818094316, 34278416330918655840201783804131603181718906590096⟩

/-- ICARM leaderboard curve 304 has Mordell-Weil rank at least `22`. -/
public theorem curve304_hasRankGE_22 : HasRankGE curve304 22 := by
  unfold curve304
  certify_curve torsion 13 "data/curve304.txt" "data/curve304-labels.txt"

/-- Curve 304 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve304.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 304. -/
public theorem curve304_j : curve304.j = 882979629965878142319403592711204222436511549801509539530594582279285465455491783133778542832948806767809 / 3379337256877848416704903412257177388986372653464337778640355908107748274947815216082189778984960000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
