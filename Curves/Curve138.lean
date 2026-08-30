/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 138 has rank at least 11

The elliptic curve recorded as
[curve 138](https://elliptic-rank.icarm.cloud/curve/138) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -34125664`   and
  `a₆ = 69523358164`

over `ℚ`. It has Mordell-Weil rank at least `11`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 138 over `ℚ`. -/
@[expose] public def curve138 : WeierstrassCurve ℚ := ⟨1, -1, 0, -34125664, 69523358164⟩

/-- ICARM leaderboard curve 138 has Mordell-Weil rank at least `11`. -/
public theorem curve138_hasRankGE_11 : HasRankGE curve138 11 := by
  unfold curve138
  certify_curve torsion 17 "data/curve138.txt" "data/curve138-labels.txt"

/-- Curve 138 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve138.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 138. -/
public theorem curve138_j : curve138.j = 4395082691371904966943770841 / 455892220051315320481372 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
