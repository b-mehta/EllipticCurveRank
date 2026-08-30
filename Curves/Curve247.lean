/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 247 has rank at least 7

The elliptic curve recorded as
[curve 247](https://elliptic-rank.icarm.cloud/curve/247) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -482829160`   and
  `a₆ = 4083394233624`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 247 over `ℚ`. -/
@[expose] public def curve247 : WeierstrassCurve ℚ := ⟨0, 1, 0, -482829160, 4083394233624⟩

/-- ICARM leaderboard curve 247 has Mordell-Weil rank at least `7`. -/
public theorem curve247_hasRankGE_7 : HasRankGE curve247 7 := by
  unfold curve247
  certify_curve torsion 11 "data/curve247.txt" "data/curve247-labels.txt"

/-- Curve 247 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve247.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 247. -/
public theorem curve247_j : curve247.j = -10126096574767163162617928 / 2093176027036499 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
