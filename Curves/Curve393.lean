/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 393 has rank at least 26

The elliptic curve recorded as
[curve 393](https://elliptic-rank.icarm.cloud/curve/393) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1741982199429864469286704668873479663123369747`   and
  `a₆ = 33616270057492031684630745788339880287409192129638100252550440305971`

over `ℚ`. It has Mordell-Weil rank at least `26`. Submitted to the leaderboard by wgxli.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 393 over `ℚ`. -/
@[expose] public def curve393 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -1741982199429864469286704668873479663123369747,
    33616270057492031684630745788339880287409192129638100252550440305971⟩

/-- ICARM leaderboard curve 393 has Mordell-Weil rank at least `26`. -/
public theorem curve393_hasRankGE_26 : HasRankGE curve393 26 := by
  unfold curve393
  certify_curve torsion 79 "data/curve393.txt" "data/curve393-labels.txt"

/-- Curve 393 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve393.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 393. -/
public theorem curve393_j : curve393.j = -9601335306273240191634386972650174809360899961258204324769841584208383116410053921120010551525069657154025574732898540656282548550569 / 2461552231353226401750043604282406323981687611130639504337041053715391242370769924272608125951250560187200689010864351757926400000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
