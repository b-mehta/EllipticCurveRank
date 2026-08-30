/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 167 has rank at least 16

The elliptic curve recorded as
[curve 167](https://elliptic-rank.icarm.cloud/curve/167) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4322087140978044344318`   and
  `a₆ = 113218873181275746647084844047757`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 167 over `ℚ`. -/
@[expose] public def curve167 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -4322087140978044344318, 113218873181275746647084844047757⟩

/-- ICARM leaderboard curve 167 has Mordell-Weil rank at least `16`. -/
public theorem curve167_hasRankGE_16 : HasRankGE curve167 16 := by
  unfold curve167
  certify_curve torsion 7 "data/curve167.txt" "data/curve167-labels.txt"

/-- Curve 167 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve167.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 167. -/
public theorem curve167_j : curve167.j = -12248326090032710479397653967897226856912283609028084419976207113881 / 508004324086258229695901640128237130508912591579698075573043200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
