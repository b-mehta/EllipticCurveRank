/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 215 has rank at least 18

The elliptic curve recorded as
[curve 215](https://elliptic-rank.icarm.cloud/curve/215) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -50968883660167848001767`   and
  `a₆ = 5184551861194511414139157441329641`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by RoyManami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 215 over `ℚ`. -/
@[expose] public def curve215 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -50968883660167848001767, 5184551861194511414139157441329641⟩

/-- ICARM leaderboard curve 215 has Mordell-Weil rank at least `18`. -/
public theorem curve215_hasRankGE_18 : HasRankGE curve215 18 := by
  unfold curve215
  certify_curve torsion 13 "data/curve215.txt" "data/curve215-labels.txt"

/-- Curve 215 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve215.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 215. -/
public theorem curve215_j : curve215.j = -1285557548034318479609724696653841069719710141900939767749424462633 / 275475969825108185987893345338322452777752095414932289353778364 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
