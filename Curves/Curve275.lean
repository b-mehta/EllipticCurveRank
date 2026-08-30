/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 275 has rank at least 20

The elliptic curve recorded as
[curve 275](https://elliptic-rank.icarm.cloud/curve/275) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -2034488389107661074627844285`   and
  `a₆ = 35847670110541831966937994064437784692732`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 275 over `ℚ`. -/
@[expose] public def curve275 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -2034488389107661074627844285, 35847670110541831966937994064437784692732⟩

/-- ICARM leaderboard curve 275 has Mordell-Weil rank at least `20`. -/
public theorem curve275_hasRankGE_20 : HasRankGE curve275 20 := by
  unfold curve275
  certify_curve torsion 5 "data/curve275.txt" "data/curve275-labels.txt"

/-- Curve 275 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve275.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 275. -/
public theorem curve275_j : curve275.j = -931299477114920794949720523496110433048090905702531271730340331493514008514128797768393 / 16197498753307130570718466689601294928007257164818990602909253701371655741958401236 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
