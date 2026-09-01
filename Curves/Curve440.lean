/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 440 has rank at least 20

The elliptic curve recorded as
[curve 440](https://elliptic-rank.icarm.cloud/curve/440) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -251999675509943915172708010850520040`   and
  `a₆ = 56079773175596610092961984688743586678074315954876992`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Nikita-Shulga.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 440 over `ℚ`. -/
@[expose] public def curve440 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -251999675509943915172708010850520040,
    56079773175596610092961984688743586678074315954876992⟩

/-- ICARM leaderboard curve 440 has Mordell-Weil rank at least `20`. -/
public theorem curve440_hasRankGE_20 : HasRankGE curve440 20 := by
  unfold curve440
  certify_curve torsion 37 "data/curve440.txt" "data/curve440-labels.txt"

/-- Curve 440 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve440.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 440. -/
public theorem curve440_j : curve440.j = -737108631416224689220583040593879933855043001173794165602649699632893394163376471490622527299135778047286561 / 139286105330723590078231981046847905076231028669888936593104158573297818981831995718666845260329369600000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
