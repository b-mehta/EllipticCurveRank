/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 203 has rank at least 13

The elliptic curve recorded as
[curve 203](https://elliptic-rank.icarm.cloud/curve/203) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -6897389822833125395`   and
  `a₆ = 7113465576836136307696346462`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 203 over `ℚ`. -/
@[expose] public def curve203 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -6897389822833125395, 7113465576836136307696346462⟩

/-- ICARM leaderboard curve 203 has Mordell-Weil rank at least `13`. -/
public theorem curve203_hasRankGE_13 : HasRankGE curve203 13 := by
  unfold curve203
  certify_curve torsion 5 "data/curve203.txt" "data/curve203-labels.txt"

/-- Curve 203 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve203.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 203. -/
public theorem curve203_j : curve203.j = -36289252941788492228014277929242790315626075343859363926982953 / 859076487022818729321026088704523026210935982019962548656 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
