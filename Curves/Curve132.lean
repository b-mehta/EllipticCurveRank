/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 132 has rank at least 9

The elliptic curve recorded as
[curve 132](https://elliptic-rank.icarm.cloud/curve/132) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -613069`   and
  `a₆ = 98885089`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve132.txt`; descent labels are in
`data/curve132-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 132 over `ℚ`. -/
@[expose] public def curve132 : WeierstrassCurve ℚ := ⟨1, -1, 0, -613069, 98885089⟩

/-- ICARM leaderboard curve 132 has Mordell-Weil rank at least `9`. -/
public theorem curve132_hasRankGE_9 : HasRankGE curve132 9 := by
  unfold curve132
  certify_curve torsion 7 "data/curve132.txt" "data/curve132-labels.txt"

/-- Curve 132 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve132.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 132. -/
public theorem curve132_j : curve132.j = 1740529703901401721 / 719625538898932 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
