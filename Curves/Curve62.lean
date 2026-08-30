/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 62 has rank at least 17

The elliptic curve recorded as
[curve 62](https://elliptic-rank.icarm.cloud/curve/62) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = -908800736629952526116772283648363`

over `ℚ`. It has Mordell-Weil rank at least `17`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 62 over `ℚ`. -/
@[expose] public def curve62 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 0, -908800736629952526116772283648363⟩

/-- ICARM leaderboard curve 62 has Mordell-Weil rank at least `17`. -/
public theorem curve62_hasRankGE_17 : HasRankGE curve62 17 := by
  unfold curve62
  certify_curve torsion 7 "data/curve62.txt" "data/curve62-labels.txt"

/-- Curve 62 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve62.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 62. -/
public theorem curve62_j : curve62.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
