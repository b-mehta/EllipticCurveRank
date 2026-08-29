/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 71 has rank at least 4

The elliptic curve recorded as
[curve 71](https://elliptic-rank.icarm.cloud/curve/71) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -75`   and
  `a₆ = -134`

over `ℚ`. It has Mordell-Weil rank at least `4`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve71.txt`; descent labels are in
`data/curve71-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 71 over `ℚ`. -/
@[expose] public def curve71 : WeierstrassCurve ℚ := ⟨0, -1, 0, -75, -134⟩

/-- ICARM leaderboard curve 71 has Mordell-Weil rank at least `4`. -/
public theorem curve71_hasRankGE_4 : HasRankGE curve71 4 := by
  unfold curve71
  certify_curve torsion 17 "data/curve71.txt" "data/curve71-labels.txt"

/-- Curve 71 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve71.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 71. -/
public theorem curve71_j : curve71.j = 2955053056 / 1026877 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
