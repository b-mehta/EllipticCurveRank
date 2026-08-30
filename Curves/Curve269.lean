/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 269 has rank at least 8

The elliptic curve recorded as
[curve 269](https://elliptic-rank.icarm.cloud/curve/269) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -2308801`   and
  `a₆ = 2365444`

over `ℚ`. It has Mordell-Weil rank at least `8`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 269 over `ℚ`. -/
@[expose] public def curve269 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2308801, 2365444⟩

/-- ICARM leaderboard curve 269 has Mordell-Weil rank at least `8`. -/
public theorem curve269_hasRankGE_8 : HasRankGE curve269 8 := by
  unfold curve269
  certify_curve torsion 19 "data/curve269.txt" "data/curve269-labels.txt"

/-- Curve 269 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve269.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 269. -/
public theorem curve269_j : curve269.j = 21266853711813353780928 / 12307169240705355733 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
