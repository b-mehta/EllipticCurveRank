/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 297 has rank at least 19

The elliptic curve recorded as
[curve 297](https://elliptic-rank.icarm.cloud/curve/297) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -102056804118937439750571852774621992`   and
  `a₆ = 12353237625156568163254531376811881758355861766631659`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 297 over `ℚ`. -/
@[expose] public def curve297 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -102056804118937439750571852774621992,
    12353237625156568163254531376811881758355861766631659⟩

/-- ICARM leaderboard curve 297 has Mordell-Weil rank at least `19`. -/
public theorem curve297_hasRankGE_19 : HasRankGE curve297 19 := by
  unfold curve297
  certify_curve torsion 17 "data/curve297.txt" "data/curve297-labels.txt"

/-- Curve 297 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve297.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 297. -/
public theorem curve297_j : curve297.j = 161258299955760047236170103522926762675371616097702341870534073861788152873683244359591102752707382168608569 / 2889676282644760701646098069901030473735322608308703495604579825568384807289002485392265357621309440000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
