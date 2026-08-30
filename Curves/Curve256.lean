/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 256 has rank at least 7

The elliptic curve recorded as
[curve 256](https://elliptic-rank.icarm.cloud/curve/256) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 47522`   and
  `a₆ = 1`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 256 over `ℚ`. -/
@[expose] public def curve256 : WeierstrassCurve ℚ := ⟨0, 0, 0, 47522, 1⟩

/-- ICARM leaderboard curve 256 has Mordell-Weil rank at least `7`. -/
public theorem curve256_hasRankGE_7 : HasRankGE curve256 7 := by
  unfold curve256
  certify_curve torsion 5 "data/curve256.txt" "data/curve256-labels.txt"

/-- Curve 256 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve256.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 256. -/
public theorem curve256_j : curve256.j = 741801759994238976 / 429283425922619 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
