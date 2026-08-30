/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 158 has rank at least 13

The elliptic curve recorded as
[curve 158](https://elliptic-rank.icarm.cloud/curve/158) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1876573260`   and
  `a₆ = 32705933898332`

over `ℚ`. It has Mordell-Weil rank at least `13`.

Submitted to the leaderboard by Andrew Sutherland.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 158 over `ℚ`. -/
@[expose] public def curve158 : WeierstrassCurve ℚ := ⟨0, -1, 1, -1876573260, 32705933898332⟩

/-- ICARM leaderboard curve 158 has Mordell-Weil rank at least `13`. -/
public theorem curve158_hasRankGE_13 : HasRankGE curve158 13 := by
  unfold curve158
  certify_curve torsion 7 "data/curve158.txt" "data/curve158-labels.txt"

/-- Curve 158 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve158.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 158. -/
public theorem curve158_j : curve158.j = -730836591023566422475539482791936 / 39145426572195170656486418763 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
