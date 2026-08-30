/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 344 has rank at least 11

The elliptic curve recorded as
[curve 344](https://elliptic-rank.icarm.cloud/curve/344) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2170332799426280`   and
  `a₆ = 38217297474283536107947`

over `ℚ`. It has Mordell-Weil rank at least `11`.

Submitted to the leaderboard by Daksh Shami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 344 over `ℚ`. -/
@[expose] public def curve344 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -2170332799426280, 38217297474283536107947⟩

/-- ICARM leaderboard curve 344 has Mordell-Weil rank at least `11`. -/
public theorem curve344_hasRankGE_11 : HasRankGE curve344 11 := by
  unfold curve344
  certify_curve torsion 7 "data/curve344.txt" "data/curve344-labels.txt"

/-- Curve 344 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve344.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 344. -/
public theorem curve344_j : curve344.j = 2481390800734615671355705055876564223641860425 / 51161095239819270776023984013087714148352 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
