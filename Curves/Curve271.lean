/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 271 has rank at least 4

The elliptic curve recorded as
[curve 271](https://elliptic-rank.icarm.cloud/curve/271) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2`   and
  `a₆ = 42`

over `ℚ`. It has Mordell-Weil rank at least `4`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 271 over `ℚ`. -/
@[expose] public def curve271 : WeierstrassCurve ℚ := ⟨0, 1, 1, -2, 42⟩

/-- ICARM leaderboard curve 271 has Mordell-Weil rank at least `4`. -/
public theorem curve271_hasRankGE_4 : HasRankGE curve271 4 := by
  unfold curve271
  certify_curve torsion 5 "data/curve271.txt" "data/curve271-labels.txt"

/-- Curve 271 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve271.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 271. -/
public theorem curve271_j : curve271.j = -1404928 / 797611 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
