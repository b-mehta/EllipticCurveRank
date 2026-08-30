/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 306 has rank at least 15

The elliptic curve recorded as
[curve 306](https://elliptic-rank.icarm.cloud/curve/306) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -190635540832861113395418678249957061673`   and
  `a₆ = 990015609814751950477026449045375925435404310567801342428`

over `ℚ`. It has Mordell-Weil rank at least `15`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 306 over `ℚ`. -/
@[expose] public def curve306 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -190635540832861113395418678249957061673,
    990015609814751950477026449045375925435404310567801342428⟩

/-- ICARM leaderboard curve 306 has Mordell-Weil rank at least `15`. -/
public theorem curve306_hasRankGE_15 : HasRankGE curve306 15 := by
  unfold curve306
  certify_curve oneTorsion 27870633504370443852 13 "data/curve306.txt" "data/curve306-labels.txt"

/-- Curve 306 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve306.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 306. -/
public theorem curve306_j : curve306.j = 5576254712865363483053752237070781870823751441932635272834295844912316983392992742007 / 145407453776393801820203291860281234365941933072529682700344994630930896663750000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
