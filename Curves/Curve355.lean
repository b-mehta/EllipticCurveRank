/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 355 has rank at least 20

The elliptic curve recorded as
[curve 355](https://elliptic-rank.icarm.cloud/curve/355) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -252855311567215820639960610648737067`   and
  `a₆ = 49319408860526775041104717131304690483461209453955226`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 355 over `ℚ`. -/
@[expose] public def curve355 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -252855311567215820639960610648737067,
    49319408860526775041104717131304690483461209453955226⟩

/-- ICARM leaderboard curve 355 has Mordell-Weil rank at least `20`. -/
public theorem curve355_hasRankGE_20 : HasRankGE curve355 20 := by
  unfold curve355
  certify_curve torsion 23 "data/curve355.txt" "data/curve355-labels.txt"

/-- Curve 355 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve355.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 355. -/
public theorem curve355_j : curve355.j = -598759585213272469834650218141939424198494810521287232606863936797473953909834551605208540901255130017769 / 5405924406643097152871863414800036170204499282075405190916903108371104984202443269706572645658954375 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
