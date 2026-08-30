/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 246 has rank at least 7

The elliptic curve recorded as
[curve 246](https://elliptic-rank.icarm.cloud/curve/246) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -75661452`   and
  `a₆ = 253314869625`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 246 over `ℚ`. -/
@[expose] public def curve246 : WeierstrassCurve ℚ := ⟨0, 0, 0, -75661452, 253314869625⟩

/-- ICARM leaderboard curve 246 has Mordell-Weil rank at least `7`. -/
public theorem curve246_hasRankGE_7 : HasRankGE curve246 7 := by
  unfold curve246
  certify_curve torsion 7 "data/curve246.txt" "data/curve246-labels.txt"

/-- Curve 246 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve246.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 246. -/
public theorem curve246_j : curve246.j = -1368922812416061639671808 / 2053594171089889 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
