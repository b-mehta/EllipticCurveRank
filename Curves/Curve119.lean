/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 119 has rank at least 6

The elliptic curve recorded as
[curve 119](https://elliptic-rank.icarm.cloud/curve/119) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -390`   and
  `a₆ = 5460`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 119 over `ℚ`. -/
@[expose] public def curve119 : WeierstrassCurve ℚ := ⟨0, 1, 1, -390, 5460⟩

/-- ICARM leaderboard curve 119 has Mordell-Weil rank at least `6`. -/
public theorem curve119_hasRankGE_6 : HasRankGE curve119 6 := by
  unfold curve119
  certify_curve torsion 13 "data/curve119.txt" "data/curve119-labels.txt"

/-- Curve 119 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve119.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 119. -/
public theorem curve119_j : curve119.j = -6577042272256 / 9694585723 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
