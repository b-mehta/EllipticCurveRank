/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 411 has rank at least 17

The elliptic curve recorded as
[curve 411](https://elliptic-rank.icarm.cloud/curve/411) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3591481020811836471011183576975460`   and
  `a₆ = 78382925089462270043272708916456341534296382563600`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Christopher R.
Hill.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 411 over `ℚ`. -/
@[expose] public def curve411 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3591481020811836471011183576975460, 78382925089462270043272708916456341534296382563600⟩

/-- ICARM leaderboard curve 411 has Mordell-Weil rank at least `17`. -/
public theorem curve411_hasRankGE_17 : HasRankGE curve411 17 := by
  unfold curve411
  certify_curve torsion 29 "data/curve411.txt" "data/curve411-labels.txt"

/-- Curve 411 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve411.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 411. -/
public theorem curve411_j : curve411.j = 5123236913165959125996458821046022691789329403888709903975601714016789184433577659389702046536476393957441 / 310678744110001122475227156478814685375156829579582715053262018879190161226305823287881164380160000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
