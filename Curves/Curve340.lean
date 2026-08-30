/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 340 has rank at least 20

The elliptic curve recorded as
[curve 340](https://elliptic-rank.icarm.cloud/curve/340) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4478863882000398277272391296`   and
  `a₆ = 114808464561400729459593498162805258984396`

over `ℚ`. It has Mordell-Weil rank at least `20`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 340 over `ℚ`. -/
@[expose] public def curve340 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -4478863882000398277272391296, 114808464561400729459593498162805258984396⟩

/-- ICARM leaderboard curve 340 has Mordell-Weil rank at least `20`. -/
public theorem curve340_hasRankGE_20 : HasRankGE curve340 20 := by
  unfold curve340
  certify_curve torsion 5 "data/curve340.txt" "data/curve340-labels.txt"

/-- Curve 340 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve340.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 340. -/
public theorem curve340_j : curve340.j = 13630123018362204255669878653878852202911501916191268565385958380709020985919167850497 / 76849466769297782831711790936994283644159673630162135892534857526817112555900196 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
