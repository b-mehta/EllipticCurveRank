/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 154 has rank at least 9

The elliptic curve recorded as
[curve 154](https://elliptic-rank.icarm.cloud/curve/154) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -3926559`   and
  `a₆ = 3073474946`

over `ℚ`. It has Mordell-Weil rank at least `9`.

Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 154 over `ℚ`. -/
@[expose] public def curve154 : WeierstrassCurve ℚ := ⟨0, 0, 0, -3926559, 3073474946⟩

/-- ICARM leaderboard curve 154 has Mordell-Weil rank at least `9`. -/
public theorem curve154_hasRankGE_9 : HasRankGE curve154 9 := by
  unfold curve154
  certify_curve torsion 5 "data/curve154.txt" "data/curve154-labels.txt"

/-- Curve 154 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve154.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 154. -/
public theorem curve154_j : curve154.j = -107625171299249590896 / 3315860894112757 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
