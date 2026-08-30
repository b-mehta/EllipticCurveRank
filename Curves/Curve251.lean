/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 251 has rank at least 5

The elliptic curve recorded as
[curve 251](https://elliptic-rank.icarm.cloud/curve/251) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -292`   and
  `a₆ = 1105`

over `ℚ`. It has Mordell-Weil rank at least `5`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 251 over `ℚ`. -/
@[expose] public def curve251 : WeierstrassCurve ℚ := ⟨0, 0, 0, -292, 1105⟩

/-- ICARM leaderboard curve 251 has Mordell-Weil rank at least `5`. -/
public theorem curve251_hasRankGE_5 : HasRankGE curve251 5 := by
  unfold curve251
  certify_curve torsion 7 "data/curve251.txt" "data/curve251-labels.txt"

/-- Curve 251 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve251.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 251. -/
public theorem curve251_j : curve251.j = 172088672256 / 66620677 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
