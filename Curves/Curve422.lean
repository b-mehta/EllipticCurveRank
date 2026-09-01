/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 422 has rank at least 18

The elliptic curve recorded as
[curve 422](https://elliptic-rank.icarm.cloud/curve/422) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -7563743114616965332438173567`   and
  `a₆ = 250105033771561875331934803308050741991591`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 422 over `ℚ`. -/
@[expose] public def curve422 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -7563743114616965332438173567, 250105033771561875331934803308050741991591⟩

/-- ICARM leaderboard curve 422 has Mordell-Weil rank at least `18`. -/
public theorem curve422_hasRankGE_18 : HasRankGE curve422 18 := by
  unfold curve422
  certify_curve torsion 19 "data/curve422.txt" "data/curve422-labels.txt"

/-- Curve 422 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve422.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 422. -/
public theorem curve422_j : curve422.j = 19931586276225127067215381770302232483056943507702111973345478218585626773608870431201 / 279717259165713988606774162116785187468839896077440593444339560641601187840000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
