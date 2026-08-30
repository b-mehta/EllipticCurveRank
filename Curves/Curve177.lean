/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 177 has rank at least 16

The elliptic curve recorded as
[curve 177](https://elliptic-rank.icarm.cloud/curve/177) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -60022613792933162126770`   and
  `a₆ = 5643374875619607135973539223008900`

over `ℚ`. It has Mordell-Weil rank at least `16`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 177 over `ℚ`. -/
@[expose] public def curve177 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -60022613792933162126770, 5643374875619607135973539223008900⟩

/-- ICARM leaderboard curve 177 has Mordell-Weil rank at least `16`. -/
public theorem curve177_hasRankGE_16 : HasRankGE curve177 16 := by
  unfold curve177
  certify_curve torsion 19 "data/curve177.txt" "data/curve177-labels.txt"

/-- Curve 177 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve177.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 177. -/
public theorem curve177_j : curve177.j = 23914891950718945755043605497931276071435002145212436790674004201328795681 / 81438791243922645157611866031099042317832628278473480004951449600000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
