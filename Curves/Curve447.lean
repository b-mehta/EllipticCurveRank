/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 447 has rank at least 20

The elliptic curve recorded as
[curve 447](https://elliptic-rank.icarm.cloud/curve/447) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -8223603166187780927160926046820690`   and
  `a₆ = 289423414197390060483587925043989774858424061454596`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 447 over `ℚ`. -/
@[expose] public def curve447 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -8223603166187780927160926046820690,
    289423414197390060483587925043989774858424061454596⟩

/-- ICARM leaderboard curve 447 has Mordell-Weil rank at least `20`. -/
public theorem curve447_hasRankGE_20 : HasRankGE curve447 20 := by
  unfold curve447
  certify_curve torsion 61 "data/curve447.txt" "data/curve447-labels.txt"

/-- Curve 447 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve447.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 447. -/
public theorem curve447_j : curve447.j = -25616393579946834599064551585756581061074454089517007448470697559422034852083498392593317825627773524161 / 247282616317408623795101740016021616420265786651031227687322434452036163296866639300228248591269888 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
