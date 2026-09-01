/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 415 has rank at least 15

The elliptic curve recorded as
[curve 415](https://elliptic-rank.icarm.cloud/curve/415) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -427670503289292`   and
  `a₆ = 3399885724607313599540`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Rayan Hatout.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 415 over `ℚ`. -/
@[expose] public def curve415 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -427670503289292, 3399885724607313599540⟩

/-- ICARM leaderboard curve 415 has Mordell-Weil rank at least `15`. -/
public theorem curve415_hasRankGE_15 : HasRankGE curve415 15 := by
  unfold curve415
  certify_curve torsion 13 "data/curve415.txt" "data/curve415-labels.txt"

/-- Curve 415 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve415.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 415. -/
public theorem curve415_j : curve415.j = 46353668615870773858773722175656352427131904 / 67579198099758366181487967147816246693 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
