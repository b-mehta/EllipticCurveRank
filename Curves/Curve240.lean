/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 240 has rank at least 19

The elliptic curve recorded as
[curve 240](https://elliptic-rank.icarm.cloud/curve/240) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -29015852737941337052556`   and
  `a₆ = 1950033817928958623296270251397996`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 240 over `ℚ`. -/
@[expose] public def curve240 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -29015852737941337052556, 1950033817928958623296270251397996⟩

/-- ICARM leaderboard curve 240 has Mordell-Weil rank at least `19`. -/
public theorem curve240_hasRankGE_19 : HasRankGE curve240 19 := by
  unfold curve240
  certify_curve torsion 5 "data/curve240.txt" "data/curve240-labels.txt"

/-- Curve 240 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve240.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 240. -/
public theorem curve240_j : curve240.j = -3705972557857231372289575910655297107980165442217318653229095850707137 / 108751445929391105693003663709330401851059569537300943313379657964 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
