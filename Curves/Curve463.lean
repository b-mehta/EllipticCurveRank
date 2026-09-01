/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 463 has rank at least 20

The elliptic curve recorded as
[curve 463](https://elliptic-rank.icarm.cloud/curve/463) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -4682646150937436689802827639391590`   and
  `a₆ = 118660653877767113794215602966189789176568569086692`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 463 over `ℚ`. -/
@[expose] public def curve463 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -4682646150937436689802827639391590,
    118660653877767113794215602966189789176568569086692⟩

/-- ICARM leaderboard curve 463 has Mordell-Weil rank at least `20`. -/
public theorem curve463_hasRankGE_20 : HasRankGE curve463 20 := by
  unfold curve463
  certify_curve torsion 23 "data/curve463.txt" "data/curve463-labels.txt"

/-- Curve 463 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve463.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 463. -/
public theorem curve463_j : curve463.j = 4729394863792962222290167609294436425538633622716134218807496274293110308359796312931271988072714357761 / 203510770269098115255541420494744710550882227444210756029536716250998213439730629848961669120000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
