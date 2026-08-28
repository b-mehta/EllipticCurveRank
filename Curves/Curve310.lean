/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 310 has rank at least 15

The elliptic curve recorded as
[curve 310](https://elliptic-rank.icarm.cloud/curve/310) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1873940813132840352272936419410635778826863`   and
  `a₆ = 987165421651192729341038595063275202627467898519141617381276217`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve310.txt`; descent labels are in
`data/curve310-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 310 over `ℚ`. -/
@[expose] public def curve310 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1873940813132840352272936419410635778826863,
    987165421651192729341038595063275202627467898519141617381276217⟩

/-- ICARM leaderboard curve 310 has Mordell-Weil rank at least `15`. -/
public theorem curve310_hasRankGE_15 : HasRankGE curve310 15 := by
  unfold curve310
  certify_curve oneTorsion 3198874389822374264783 61 "data/curve310.txt" "data/curve310-labels.txt"

/-- Curve 310 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve310.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 310. -/
public theorem curve310_j : curve310.j = 4909177350729284994963348684631137965783551480274057204222984100668813009953631678328881822209262561202416791352565341 / 1203180591138217172482841236268420464298540626014571575872088258687775595250978983478973396509743433591763366272 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
