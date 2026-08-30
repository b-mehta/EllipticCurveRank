/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 146 has rank at least 18

The elliptic curve recorded as
[curve 146](https://elliptic-rank.icarm.cloud/curve/146) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -5556025348607281549409726`   and
  `a₆ = 4850907150606399626446672370423348348`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 146 over `ℚ`. -/
@[expose] public def curve146 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -5556025348607281549409726, 4850907150606399626446672370423348348⟩

/-- ICARM leaderboard curve 146 has Mordell-Weil rank at least `18`. -/
public theorem curve146_hasRankGE_18 : HasRankGE curve146 18 := by
  unfold curve146
  certify_curve torsion 23 "data/curve146.txt" "data/curve146-labels.txt"

/-- Curve 146 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve146.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 146. -/
public theorem curve146_j : curve146.j = 1213937539240224171360397878452987978473182047048439155869853484629916363217 / 51916762541332422595394109101873175611979790815209442814272781969211364 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
