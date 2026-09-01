/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 91 has rank at least 16

The elliptic curve recorded as
[curve 91](https://elliptic-rank.icarm.cloud/curve/91) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -6540850922519953718`   and
  `a₆ = -1851537704759959591812063912`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 91 over `ℚ`. -/
@[expose] public def curve091 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -6540850922519953718, -1851537704759959591812063912⟩

/-- ICARM leaderboard curve 91 has Mordell-Weil rank at least `16`. -/
public theorem curve091_hasRankGE_16 : HasRankGE curve091 16 := by
  unfold curve091
  certify_curve torsion 13 "data/curve091.txt" "data/curve091-labels.txt"

/-- Curve 91 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve091.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 91. -/
public theorem curve091_j : curve091.j = 30947563652362361354885306222716683691704252309624582244344169 / 16428490821820205276811409387619951769804980047294386996300 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
