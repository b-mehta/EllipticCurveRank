/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 73 has rank at least 18

The elliptic curve recorded as
[curve 73](https://elliptic-rank.icarm.cloud/curve/73) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -131092767138360259739530662694875901594863`   and
  `a₆ = 11513825206543517171066572416002846205241167788788151682092217`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 73 over `ℚ`. -/
@[expose] public def curve73 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -131092767138360259739530662694875901594863,
    11513825206543517171066572416002846205241167788788151682092217⟩

/-- ICARM leaderboard curve 73 has Mordell-Weil rank at least `18`. -/
public theorem curve73_hasRankGE_18 : HasRankGE curve73 18 := by
  unfold curve73
  certify_curve oneTorsion (-1599437194911187132392) 13 "data/curve73.txt" "data/curve73-labels.txt"

/-- Curve 73 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve73.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 73. -/
public theorem curve73_j : curve73.j = 1680650094760075832375792186207105980231695336102201698790092916703099329537832635384474592916981749350524551013981 / 586284466816895441725016823462228572336614970829564783090569981377101688741165246294300633474434802231794941952 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
