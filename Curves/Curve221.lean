/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 221 has rank at least 14

The elliptic curve recorded as
[curve 221](https://elliptic-rank.icarm.cloud/curve/221) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1771379373053841538`   and
  `a₆ = 922565642019656180361670031`

over `ℚ`. It has Mordell-Weil rank at least `14`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 221 over `ℚ`. -/
@[expose] public def curve221 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1771379373053841538, 922565642019656180361670031⟩

/-- ICARM leaderboard curve 221 has Mordell-Weil rank at least `14`. -/
public theorem curve221_hasRankGE_14 : HasRankGE curve221 14 := by
  unfold curve221
  certify_curve torsion 7 "data/curve221.txt" "data/curve221-labels.txt"

/-- Curve 221 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve221.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 221. -/
public theorem curve221_j : curve221.j = -39340369594740395467200454413280409229066886497288082777 / 765551803417406517297587327696887171390813932527616 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
