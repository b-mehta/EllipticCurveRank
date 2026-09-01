/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 437 has rank at least 20

The elliptic curve recorded as
[curve 437](https://elliptic-rank.icarm.cloud/curve/437) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -20461874431447421784527688374633158`   and
  `a₆ = 1127554729426977874077743817330162797017594385944556`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 437 over `ℚ`. -/
@[expose] public def curve437 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -20461874431447421784527688374633158,
    1127554729426977874077743817330162797017594385944556⟩

/-- ICARM leaderboard curve 437 has Mordell-Weil rank at least `20`. -/
public theorem curve437_hasRankGE_20 : HasRankGE curve437 20 := by
  unfold curve437
  certify_curve torsion 17 "data/curve437.txt" "data/curve437-labels.txt"

/-- Curve 437 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve437.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 437. -/
public theorem curve437_j : curve437.j = -947457979406256461530214236380587424077455035546687589816298059913858411054913032616286846598779082133291481 / 938574726530719210755177966086236778183778997655149161845867777826842521457027328930277609978004062500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
