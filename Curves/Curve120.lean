/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 120 has rank at least 7

The elliptic curve recorded as
[curve 120](https://elliptic-rank.icarm.cloud/curve/120) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -14733`   and
  `a₆ = 694232`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 120 over `ℚ`. -/
@[expose] public def curve120 : WeierstrassCurve ℚ := ⟨1, 0, 1, -14733, 694232⟩

/-- ICARM leaderboard curve 120 has Mordell-Weil rank at least `7`. -/
public theorem curve120_hasRankGE_7 : HasRankGE curve120 7 := by
  unfold curve120
  certify_curve torsion 7 "data/curve120.txt" "data/curve120-labels.txt"

/-- Curve 120 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve120.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 120. -/
public theorem curve120_j : curve120.j = -353634725049614281 / 4293362725648 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
