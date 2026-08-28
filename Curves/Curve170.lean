/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 170 has rank at least 16

The elliptic curve recorded as
[curve 170](https://elliptic-rank.icarm.cloud/curve/170) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1002421447003943457225`   and
  `a₆ = 12481234946887000688835790191735`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve170.txt`; descent labels are in
`data/curve170-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 170 over `ℚ`. -/
@[expose] public def curve170 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -1002421447003943457225, 12481234946887000688835790191735⟩

/-- ICARM leaderboard curve 170 has Mordell-Weil rank at least `16`. -/
public theorem curve170_hasRankGE_16 : HasRankGE curve170 16 := by
  unfold curve170
  certify_curve torsion 53 "data/curve170.txt" "data/curve170-labels.txt"

/-- Curve 170 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve170.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 170. -/
public theorem curve170_j : curve170.j = -111397324908611358472324907164906355881199517169909894811836380560401 / 2831445042543812469319980404169211270210294978426890329088000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
