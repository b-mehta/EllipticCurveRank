/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 378 has rank at least 24

The elliptic curve recorded as
[curve 378](https://elliptic-rank.icarm.cloud/curve/378) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -3896830274733436253799445060729628270620`   and
  `a₆ = 93850226586476646888800893430393312604104981963137354427600`

over `ℚ`. It has Mordell-Weil rank at least `24`.

Submitted to the leaderboard by wgxli.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 378 over `ℚ`. -/
@[expose] public def curve378 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -3896830274733436253799445060729628270620,
    93850226586476646888800893430393312604104981963137354427600⟩

/-- ICARM leaderboard curve 378 has Mordell-Weil rank at least `24`. -/
public theorem curve378_hasRankGE_24 : HasRankGE curve378 24 := by
  unfold curve378
  certify_curve torsion 7 "data/curve378.txt" "data/curve378-labels.txt"

/-- Curve 378 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve378.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 378. -/
public theorem curve378_j : curve378.j = -25563376636988401920872712436183753485261168252215741207856607208880091451776944175899435311739715124325563309438516326096 / 69651499689033310599477700552365182969329108566516764990738938069452593816146500869269694450585881805144754933046875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
