/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 66 has rank at least 26

The elliptic curve recorded as
[curve 66](https://elliptic-rank.icarm.cloud/curve/66) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -271568164801421919805097494520335727505515190`   and
  `a₆ = 1673523352045742769296938739782713519216640490554763586630258973092`

over `ℚ`. It has Mordell-Weil rank at least `26`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 66 over `ℚ`. -/
@[expose] public def curve66 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -271568164801421919805097494520335727505515190,
    1673523352045742769296938739782713519216640490554763586630258973092⟩

/-- ICARM leaderboard curve 66 has Mordell-Weil rank at least `26`. -/
public theorem curve66_hasRankGE_26 : HasRankGE curve66 26 := by
  unfold curve66
  certify_curve torsion 23 "data/curve66.txt" "data/curve66-labels.txt"

/-- Curve 66 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve66.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 66. -/
public theorem curve66_j : curve66.j = 2214931422688513257204841031697884573324167341560076198204430123619213413222688639063521706435446535737828256930906898489685579245776638561 / 71895080707631236566227414257088729466603817414726942045972724673173251962604021806427843161273966232348946866110784725884544768000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
