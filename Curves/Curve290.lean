/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 290 has rank at least 19

The elliptic curve recorded as
[curve 290](https://elliptic-rank.icarm.cloud/curve/290) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -143064121313070058971349202`   and
  `a₆ = 644033892656805018000831946914423333329`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 290 over `ℚ`. -/
@[expose] public def curve290 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -143064121313070058971349202, 644033892656805018000831946914423333329⟩

/-- ICARM leaderboard curve 290 has Mordell-Weil rank at least `19`. -/
public theorem curve290_hasRankGE_19 : HasRankGE curve290 19 := by
  unfold curve290
  certify_curve torsion 31 "data/curve290.txt" "data/curve290-labels.txt"

/-- Curve 290 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve290.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 290. -/
public theorem curve290_j : curve290.j = 444210049222489621477608429562013018012674903372400794907658987789496747104083929 / 11270649661159432034309229020483247353533212692858049368372285851855011840000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
