/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 443 has rank at least 19

The elliptic curve recorded as
[curve 443](https://elliptic-rank.icarm.cloud/curve/443) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -470205160918761195421530423911518748067291843154934193054292446585122015228`
  `     136823`   and
  `a₆ = 3790838284044638260603760507410155823669268918149579764831861050275267231873`
  `     985142865201191329587809161081790942820131278`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by Nikita-Shulga.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 443 over `ℚ`. -/
@[expose] public def curve443 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -470205160918761195421530423911518748067291843154934193054292446585122015228136823,
    3790838284044638260603760507410155823669268918149579764831861050275267231873985142865201191329587809161081790942820131278⟩

/-- ICARM leaderboard curve 443 has Mordell-Weil rank at least `19`. -/
public theorem curve443_hasRankGE_19 : HasRankGE curve443 19 := by
  unfold curve443
  certify_curve torsion 17 "data/curve443.txt" "data/curve443-labels.txt"

/-- Curve 443 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve443.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 443. -/
public theorem curve443_j : curve443.j = 4788436436610594767147441315235065931877113453062171122318601223033567483463297721059277582657227867235840934619120710249926857276489759603357689727416082102625680673649359540014508229002864894893964617716650355622430204383427320621445411967241 / 185481354803692124412450607380085105761250887880637472713962629792849835696493142406069626135241448312772074077762704013735692384157902281235082042649933084181814139695120007696777733907597833834008937150238806531555529721926041155130937500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
