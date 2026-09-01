/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 402 has rank at least 27

The elliptic curve recorded as
[curve 402](https://elliptic-rank.icarm.cloud/curve/402) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -12726070774451041281283293178772853133737609104772`   and
  `a₆ = 17471855868336653804432728505912897769345397163476843729857408410639782695`

over `ℚ`. It has Mordell-Weil rank at least `27`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 402 over `ℚ`. -/
@[expose] public def curve402 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -12726070774451041281283293178772853133737609104772,
    17471855868336653804432728505912897769345397163476843729857408410639782695⟩

/-- ICARM leaderboard curve 402 has Mordell-Weil rank at least `27`. -/
public theorem curve402_hasRankGE_27 : HasRankGE curve402 27 := by
  unfold curve402
  certify_curve torsion 19 "data/curve402.txt" "data/curve402-labels.txt"

/-- Curve 402 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve402.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 402. -/
public theorem curve402_j : curve402.j = 881959403909285231319082847968048928560600868901743589485433349389895828529780806807287306696002812047482115710736853478405489750111478850161 / 118863489579747294601562307975854039223806485383689751590773200973472036282478261622766026162599397919637527691986811759961572467802112 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
