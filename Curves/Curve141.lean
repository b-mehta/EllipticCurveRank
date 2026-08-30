/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 141 has rank at least 16

The elliptic curve recorded as
[curve 141](https://elliptic-rank.icarm.cloud/curve/141) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -6254103958828689783047`   and
  `a₆ = 192644462377949614527629133622271`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 141 over `ℚ`. -/
@[expose] public def curve141 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -6254103958828689783047, 192644462377949614527629133622271⟩

/-- ICARM leaderboard curve 141 has Mordell-Weil rank at least `16`. -/
public theorem curve141_hasRankGE_16 : HasRankGE curve141 16 := by
  unfold curve141
  certify_curve torsion 31 "data/curve141.txt" "data/curve141-labels.txt"

/-- Curve 141 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve141.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 141. -/
public theorem curve141_j : curve141.j = -37110044223081690097367665230553544486755946267474321567766859966249 / 516510413442146499141074184196230628833010080720238510080000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
