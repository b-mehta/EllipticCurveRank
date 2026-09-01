/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 458 has rank at least 20

The elliptic curve recorded as
[curve 458](https://elliptic-rank.icarm.cloud/curve/458) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -24459647223008819321132521677571770`   and
  `a₆ = 1475866115712309323058485904595825308688025746908900`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 458 over `ℚ`. -/
@[expose] public def curve458 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -24459647223008819321132521677571770,
    1475866115712309323058485904595825308688025746908900⟩

/-- ICARM leaderboard curve 458 has Mordell-Weil rank at least `20`. -/
public theorem curve458_hasRankGE_20 : HasRankGE curve458 20 := by
  unfold curve458
  certify_curve torsion 23 "data/curve458.txt" "data/curve458-labels.txt"

/-- Curve 458 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve458.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 458. -/
public theorem curve458_j : curve458.j = -674034488956269623721207878800586734701433300199281762423830633666053352424179825237737577801415191401281 / 1842991768803466200742625267256783878803029812388071844790407549889254568497409026264202594560000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
