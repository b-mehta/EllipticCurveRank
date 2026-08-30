/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 90 has rank at least 19

The elliptic curve recorded as
[curve 90](https://elliptic-rank.icarm.cloud/curve/90) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1049634928262201481608261153`   and
  `a₆ = 12127108227154239133795359409449990039537`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 90 over `ℚ`. -/
@[expose] public def curve90 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -1049634928262201481608261153, 12127108227154239133795359409449990039537⟩

/-- ICARM leaderboard curve 90 has Mordell-Weil rank at least `19`. -/
public theorem curve90_hasRankGE_19 : HasRankGE curve90 19 := by
  unfold curve90
  certify_curve torsion 41 "data/curve90.txt" "data/curve90-labels.txt"

/-- Curve 90 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve90.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 90. -/
public theorem curve90_j : curve90.j = 175432885286275280828360086171364125801928024075457989071778599235917469160397181641 / 14372991457346687754879118051280747837393220166817880670919159128474083891609600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
