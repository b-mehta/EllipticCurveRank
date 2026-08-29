/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 72 has rank at least 4

The elliptic curve recorded as
[curve 72](https://elliptic-rank.icarm.cloud/curve/72) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -7`   and
  `a₆ = 36`

over `ℚ`. It has Mordell-Weil rank at least `4`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve72.txt`; descent labels are in
`data/curve72-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 72 over `ℚ`. -/
@[expose] public def curve72 : WeierstrassCurve ℚ := ⟨0, 0, 1, -7, 36⟩

/-- ICARM leaderboard curve 72 has Mordell-Weil rank at least `4`. -/
public theorem curve72_hasRankGE_4 : HasRankGE curve72 4 := by
  unfold curve72
  certify_curve torsion 7 "data/curve72.txt" "data/curve72-labels.txt"

/-- Curve 72 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve72.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 72. -/
public theorem curve72_j : curve72.j = -37933056 / 545723 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
