/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 448 has rank at least 20

The elliptic curve recorded as
[curve 448](https://elliptic-rank.icarm.cloud/curve/448) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -74494006217084732231494701201553460`   and
  `a₆ = 7786959773639428479142830515805837724808339207958672`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 448 over `ℚ`. -/
@[expose] public def curve448 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -74494006217084732231494701201553460,
    7786959773639428479142830515805837724808339207958672⟩

/-- ICARM leaderboard curve 448 has Mordell-Weil rank at least `20`. -/
public theorem curve448_hasRankGE_20 : HasRankGE curve448 20 := by
  unfold curve448
  certify_curve torsion 19 "data/curve448.txt" "data/curve448-labels.txt"

/-- Curve 448 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve448.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 448. -/
public theorem curve448_j : curve448.j = 45718050673879255954601043542335061874155660095220454641675059285189067036374434744209719398222412574991109441 / 262132484055168836760776897065169957848979652219168298752992435420665593103233127060118979791769600000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
