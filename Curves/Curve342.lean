/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 342 has rank at least 19

The elliptic curve recorded as
[curve 342](https://elliptic-rank.icarm.cloud/curve/342) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1391553064700695297387537864163`   and
  `a₆ = 632237601708869371752246880018016126067921281`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 342 over `ℚ`. -/
@[expose] public def curve342 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1391553064700695297387537864163, 632237601708869371752246880018016126067921281⟩

/-- ICARM leaderboard curve 342 has Mordell-Weil rank at least `19`. -/
public theorem curve342_hasRankGE_19 : HasRankGE curve342 19 := by
  unfold curve342
  certify_curve torsion 13 "data/curve342.txt" "data/curve342-labels.txt"

/-- Curve 342 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve342.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 342. -/
public theorem curve342_j : curve342.j = -19072297061661906233771206794438138147139792092705583902100207882252073076156931994881342057 / 14370849162198941469327508393310482958635155172283852397156245276330989449210056441856 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
