/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 39 has rank at least 19

The elliptic curve recorded as
[curve 39](https://elliptic-rank.icarm.cloud/curve/39) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = 31368015812338065133318565292206590792820353345`   and
  `a₆ = 302038802698566087335643188429543498624522041683874493555186062568159847`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 39 over `ℚ`. -/
@[expose] public def curve039 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, 31368015812338065133318565292206590792820353345,
    302038802698566087335643188429543498624522041683874493555186062568159847⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 39 has Mordell-Weil rank at least `19`. -/
public theorem curve039_hasRankGE_19 : HasRankGE curve039 19 := by
  unfold curve039
  certify_curve oneTorsion (-2621459647861193071020724) 11 "data/curve039.txt" "data/curve039-labels.txt"

/-- Curve 39 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve039.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 39. -/
public theorem curve039_j : curve039.j = 11166714987988631433770752089762149263900173110008697045411619143221753369040120408712331453941003351880580234606318769303517 / 128935221019843919926936505048972444703354620368589547968947762946200844860380728722990780499616664872481573760750031904702464 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
