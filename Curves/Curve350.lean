/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 350 has rank at least 7

The elliptic curve recorded as
[curve 350](https://elliptic-rank.icarm.cloud/curve/350) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -13546745`   and
  `a₆ = 19183095339`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 350 over `ℚ`. -/
@[expose] public def curve350 : WeierstrassCurve ℚ := ⟨0, 1, 0, -13546745, 19183095339⟩

/-- ICARM leaderboard curve 350 has Mordell-Weil rank at least `7`. -/
public theorem curve350_hasRankGE_7 : HasRankGE curve350 7 := by
  unfold curve350
  certify_curve torsion 7 "data/curve350.txt" "data/curve350-labels.txt"

/-- Curve 350 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve350.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 350. -/
public theorem curve350_j : curve350.j = 1073961335846196311428096 / 227956011602757957 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
