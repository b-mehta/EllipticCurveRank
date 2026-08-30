/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 280 has rank at least 19

The elliptic curve recorded as
[curve 280](https://elliptic-rank.icarm.cloud/curve/280) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1475758023603928900220439411`   and
  `a₆ = 21467548255862634426152509047650717315889`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by André Röhrig.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 280 over `ℚ`. -/
@[expose] public def curve280 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1475758023603928900220439411, 21467548255862634426152509047650717315889⟩

/-- ICARM leaderboard curve 280 has Mordell-Weil rank at least `19`. -/
public theorem curve280_hasRankGE_19 : HasRankGE curve280 19 := by
  unfold curve280
  certify_curve torsion 29 "data/curve280.txt" "data/curve280-labels.txt"

/-- Curve 280 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve280.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 280. -/
public theorem curve280_j : curve280.j = 355442349958907720572845725870472793996110850510066149739983321230400707194712680813489 / 6606173027470846981780960330759477153956670797167107093900274692986568514047180800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
