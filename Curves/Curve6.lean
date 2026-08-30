/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 6 has rank at least 19

The elliptic curve recorded as
[curve 6](https://elliptic-rank.icarm.cloud/curve/6) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2063758701246626370773726978`   and
  `a₆ = 32838647793306133075103747085833809114881`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 6 over `ℚ`. -/
@[expose] public def curve6 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -2063758701246626370773726978, 32838647793306133075103747085833809114881⟩

/-- ICARM leaderboard curve 6 has Mordell-Weil rank at least `19`. -/
public theorem curve6_hasRankGE_19 : HasRankGE curve6 19 := by
  unfold curve6
  certify_curve torsion 31 "data/curve6.txt" "data/curve6-labels.txt"

/-- Curve 6 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve6.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 6. -/
public theorem curve6_j : curve6.j = 1333438333072655800326576346053542744191520910532032219284532006731512699546815066841 / 132627604887993808721569697584392184353609155330366997097523327475919340037734400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
