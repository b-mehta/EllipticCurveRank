/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 270 has rank at least 4

The elliptic curve recorded as
[curve 270](https://elliptic-rank.icarm.cloud/curve/270) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = 18`   and
  `a₆ = 121`

over `ℚ`. It has Mordell-Weil rank at least `4`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve270.txt`; descent labels are in
`data/curve270-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 270 over `ℚ`. -/
@[expose] public def curve270 : WeierstrassCurve ℚ := ⟨0, 1, 0, 18, 121⟩

/-- ICARM leaderboard curve 270 has Mordell-Weil rank at least `4`. -/
public theorem curve270_hasRankGE_4 : HasRankGE curve270 4 := by
  unfold curve270
  certify_curve torsion 5 "data/curve270.txt" "data/curve270-labels.txt"

/-- Curve 270 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve270.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 270. -/
public theorem curve270_j : curve270.j = 38112512 / 379591 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
