/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 268 has rank at least 5

The elliptic curve recorded as
[curve 268](https://elliptic-rank.icarm.cloud/curve/268) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -139`   and
  `a₆ = 72`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve268.txt`; descent labels are in
`data/curve268-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 268 over `ℚ`. -/
@[expose] public def curve268 : WeierstrassCurve ℚ := ⟨0, 0, 1, -139, 72⟩

/-- ICARM leaderboard curve 268 has Mordell-Weil rank at least `5`. -/
public theorem curve268_hasRankGE_5 : HasRankGE curve268 5 := by
  unfold curve268
  certify_curve torsion 5 "data/curve268.txt" "data/curve268-labels.txt"

/-- Curve 268 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve268.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 268. -/
public theorem curve268_j : curve268.j = 297007976448 / 169624549 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
