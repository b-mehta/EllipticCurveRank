/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 152 has rank at least 9

The elliptic curve recorded as
[curve 152](https://elliptic-rank.icarm.cloud/curve/152) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1495909`   and
  `a₆ = 697025989`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 152 over `ℚ`. -/
@[expose] public def curve152 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1495909, 697025989⟩

/-- ICARM leaderboard curve 152 has Mordell-Weil rank at least `9`. -/
public theorem curve152_hasRankGE_9 : HasRankGE curve152 9 := by
  unfold curve152
  certify_curve torsion 7 "data/curve152.txt" "data/curve152-labels.txt"

/-- Curve 152 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve152.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 152. -/
public theorem curve152_j : curve152.j = 370202545542100435703721 / 4577605239223007632 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
