/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 461 has rank at least 8

The elliptic curve recorded as
[curve 461](https://elliptic-rank.icarm.cloud/curve/461) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -5371828`   and
  `a₆ = 4980588448`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 461 over `ℚ`. -/
@[expose] public def curve461 : WeierstrassCurve ℚ := ⟨0, 0, 0, -5371828, 4980588448⟩

/-- ICARM leaderboard curve 461 has Mordell-Weil rank at least `8`. -/
public theorem curve461_hasRankGE_8 : HasRankGE curve461 8 := by
  unfold curve461
  certify_curve torsion 7 "data/curve461.txt" "data/curve461-labels.txt"

/-- Curve 461 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve461.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 461. -/
public theorem curve461_j : curve461.j = -3144502935208805184 / 145918427142925 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
