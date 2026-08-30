/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 332 has rank at least 19

The elliptic curve recorded as
[curve 332](https://elliptic-rank.icarm.cloud/curve/332) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -87896211291767885909452033582`   and
  `a₆ = 10032036623674987328062504411246312614248555`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 332 over `ℚ`. -/
@[expose] public def curve332 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -87896211291767885909452033582, 10032036623674987328062504411246312614248555⟩

/-- ICARM leaderboard curve 332 has Mordell-Weil rank at least `19`. -/
public theorem curve332_hasRankGE_19 : HasRankGE curve332 19 := by
  unfold curve332
  certify_curve torsion 5 "data/curve332.txt" "data/curve332-labels.txt"

/-- Curve 332 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve332.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 332. -/
public theorem curve332_j : curve332.j = -75099004244102664596789411022909516721866737293686914992578014052525349889794248524649833953 / 17167909180637480883395526936559530872769554325924464584539224547488746121889587183616 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
