/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 15 has rank at least 4

The elliptic curve recorded as
[curve 15](https://elliptic-rank.icarm.cloud/curve/15) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -856967076`   and
  `a₆ = 0`

over `ℚ`. It has Mordell-Weil rank at least `4`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 15 over `ℚ`. -/
@[expose] public def curve15 : WeierstrassCurve ℚ := ⟨0, 0, 0, -856967076, 0⟩

/-- ICARM leaderboard curve 15 has Mordell-Weil rank at least `4`. -/
public theorem curve15_hasRankGE_4 : HasRankGE curve15 4 := by
  unfold curve15
  certify_curve fullTorsion "data/curve15.txt" "data/curve15-labels.txt"

/-- Curve 15 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve15.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 15. -/
public theorem curve15_j : curve15.j = 1728 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
