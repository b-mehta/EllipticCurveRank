/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 347 has rank at least 19

The elliptic curve recorded as
[curve 347](https://elliptic-rank.icarm.cloud/curve/347) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -7825076977946661057500886536`   and
  `a₆ = 267129303320099174770669569025143803236416`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve347.txt`; descent labels are in
`data/curve347-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 347 over `ℚ`. -/
@[expose] public def curve347 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -7825076977946661057500886536, 267129303320099174770669569025143803236416⟩

/-- ICARM leaderboard curve 347 has Mordell-Weil rank at least `19`. -/
public theorem curve347_hasRankGE_19 : HasRankGE curve347 19 := by
  unfold curve347
  certify_curve torsion 7 "data/curve347.txt" "data/curve347-labels.txt"

/-- Curve 347 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve347.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 347. -/
public theorem curve347_j : curve347.j = -4355179504147707585338548130187121368084098358560975971546027103623134870258652822967 / 13272126561054469330475458780620623752126222124600173283207697583909882350796800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
