/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 465 has rank at least 20

The elliptic curve recorded as
[curve 465](https://elliptic-rank.icarm.cloud/curve/465) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1081299566142772205522196792975080`   and
  `a₆ = 13444054816725382360652400584113824513310769285547`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 465 over `ℚ`. -/
@[expose] public def curve465 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -1081299566142772205522196792975080,
    13444054816725382360652400584113824513310769285547⟩

/-- ICARM leaderboard curve 465 has Mordell-Weil rank at least `20`. -/
public theorem curve465_hasRankGE_20 : HasRankGE curve465 20 := by
  unfold curve465
  certify_curve torsion 59 "data/curve465.txt" "data/curve465-labels.txt"

/-- Curve 465 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve465.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 465. -/
public theorem curve465_j : curve465.j = 12274794893948050322334853650426880322392729729599967583907738094347459229895240419876854252660913 / 248638432031797501166974865532936683643162158799020370206477337793005420967608529931179524096 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
