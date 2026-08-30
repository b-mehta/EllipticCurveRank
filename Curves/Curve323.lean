/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 323 has rank at least 19

The elliptic curve recorded as
[curve 323](https://elliptic-rank.icarm.cloud/curve/323) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -488583200914951350174059380727`   and
  `a₆ = 139655693690206399673338390777234389000152361`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 323 over `ℚ`. -/
@[expose] public def curve323 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -488583200914951350174059380727, 139655693690206399673338390777234389000152361⟩

/-- ICARM leaderboard curve 323 has Mordell-Weil rank at least `19`. -/
public theorem curve323_hasRankGE_19 : HasRankGE curve323 19 := by
  unfold curve323
  certify_curve torsion 5 "data/curve323.txt" "data/curve323-labels.txt"

/-- Curve 323 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve323.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 323. -/
public theorem curve323_j : curve323.j = -12898502833945465541569569057285369753329029640934501685283689320049998807683610775826576332273 / 961192558763116104494174560156552740369599525184419354704623810269290750248214752575717376 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
