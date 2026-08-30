/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 173 has rank at least 16

The elliptic curve recorded as
[curve 173](https://elliptic-rank.icarm.cloud/curve/173) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2834094933042959558723113`   and
  `a₆ = 1836350162256247293173176506110827031`

over `ℚ`. It has Mordell-Weil rank at least `16`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 173 over `ℚ`. -/
@[expose] public def curve173 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -2834094933042959558723113, 1836350162256247293173176506110827031⟩

/-- ICARM leaderboard curve 173 has Mordell-Weil rank at least `16`. -/
public theorem curve173_hasRankGE_16 : HasRankGE curve173 16 := by
  unfold curve173
  certify_curve torsion 29 "data/curve173.txt" "data/curve173-labels.txt"

/-- Curve 173 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve173.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 173. -/
public theorem curve173_j : curve173.j = 161119040527647852163929023068926433747235212920516305289784520284239058633 / 6099809981089129676651516316527461695505967731631551375750008846336 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
