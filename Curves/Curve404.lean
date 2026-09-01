/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 404 has rank at least 27

The elliptic curve recorded as
[curve 404](https://elliptic-rank.icarm.cloud/curve/404) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -19287996132928291523665979159101108205455355568716415`   and
  `a₆ = 9833518687309329851166498536014746468879314964902591487830137954706462860306`
  `     17`

over `ℚ`. It has Mordell-Weil rank at least `27`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 404 over `ℚ`. -/
@[expose] public def curve404 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -19287996132928291523665979159101108205455355568716415,
    983351868730932985116649853601474646887931496490259148783013795470646286030617⟩

/-- ICARM leaderboard curve 404 has Mordell-Weil rank at least `27`. -/
public theorem curve404_hasRankGE_27 : HasRankGE curve404 27 := by
  unfold curve404
  certify_curve torsion 23 "data/curve404.txt" "data/curve404-labels.txt"

/-- Curve 404 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve404.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 404. -/
public theorem curve404_j : curve404.j = 330516300460980338868603673940911880634024805013711735057128811449181724677962707954891441699250458435823537644700553303377490936341650037404957310755787084561 / 17286938980387068767905529506827102316946101971268376456175599425046441674278749649162553369855385650161407470480128358617189613530746843118887816294400000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
