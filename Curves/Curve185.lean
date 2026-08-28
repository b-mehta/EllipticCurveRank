/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 185 has rank at least 16

The elliptic curve recorded as
[curve 185](https://elliptic-rank.icarm.cloud/curve/185) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -13926389068853423234936756`   and
  `a₆ = 18667175679332355979688921260281429136`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve185.txt`; descent labels are in
`data/curve185-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 185 over `ℚ`. -/
@[expose] public def curve185 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -13926389068853423234936756, 18667175679332355979688921260281429136⟩

/-- ICARM leaderboard curve 185 has Mordell-Weil rank at least `16`. -/
public theorem curve185_hasRankGE_16 : HasRankGE curve185 16 := by
  unfold curve185
  certify_curve torsion 31 "data/curve185.txt" "data/curve185-labels.txt"

/-- Curve 185 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve185.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 185. -/
public theorem curve185_j : curve185.j = 298702793708306351409820610114528715596656360389083735968302163115850761586869569 / 22324203557420732705257905143620661610548249883929708008721170067485403955200 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
