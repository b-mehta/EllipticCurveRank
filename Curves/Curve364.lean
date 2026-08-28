/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 364 has rank at least 28

The elliptic curve recorded as
[curve 364](https://elliptic-rank.icarm.cloud/curve/364) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -130750086100690559519772647173975676256671070075535710`   and
  `a₆ = 1838483676927967009646455732053953796610285093822964423352219275603069842666`
  `     1787`

over `ℚ`. It has Mordell-Weil rank at least `28`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve364.txt`; descent labels are in
`data/curve364-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 364 over `ℚ`. -/
@[expose] public def curve364 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -130750086100690559519772647173975676256671070075535710,
    18384836769279670096464557320539537966102850938229644233522192756030698426661787⟩

/-- ICARM leaderboard curve 364 has Mordell-Weil rank at least `28`. -/
public theorem curve364_hasRankGE_28 : HasRankGE curve364 28 := by
  unfold curve364
  certify_curve torsion 41 "data/curve364.txt" "data/curve364-labels.txt"

/-- Curve 364 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve364.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 364. -/
public theorem curve364_j : curve364.j = -247200680930599689249948895672953364965861756286398821354763526266081323051273848933921357481949064706955545562634446695919059990591700690308340415741092969357193441 / 2961010737665381694238613317467592451754758483359953191258113526268782917400825037154831811985806378694418704889772150842685729834590642700867701289591040000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
