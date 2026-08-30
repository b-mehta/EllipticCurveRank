/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 136 has rank at least 11

The elliptic curve recorded as
[curve 136](https://elliptic-rank.icarm.cloud/curve/136) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -38099014`   and
  `a₆ = 115877816224`

over `ℚ`. It has Mordell-Weil rank at least `11`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 136 over `ℚ`. -/
@[expose] public def curve136 : WeierstrassCurve ℚ := ⟨1, -1, 0, -38099014, 115877816224⟩

/-- ICARM leaderboard curve 136 has Mordell-Weil rank at least `11`. -/
public theorem curve136_hasRankGE_11 : HasRankGE curve136 11 := by
  unfold curve136
  certify_curve torsion 7 "data/curve136.txt" "data/curve136-labels.txt"

/-- Curve 136 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve136.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 136. -/
public theorem curve136_j : curve136.j = -6115964099629851060556637241 / 2260468062124654228043228 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
