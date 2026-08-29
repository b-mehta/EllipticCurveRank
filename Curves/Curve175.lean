/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 175 has rank at least 16

The elliptic curve recorded as
[curve 175](https://elliptic-rank.icarm.cloud/curve/175) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -29126329596087483849125163`   and
  `a₆ = 62423713413815642823213203923492112817`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve175.txt`; descent labels are in
`data/curve175-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 175 over `ℚ`. -/
@[expose] public def curve175 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -29126329596087483849125163, 62423713413815642823213203923492112817⟩

/-- ICARM leaderboard curve 175 has Mordell-Weil rank at least `16`. -/
public theorem curve175_hasRankGE_16 : HasRankGE curve175 16 := by
  unfold curve175
  certify_curve torsion 7 "data/curve175.txt" "data/curve175-labels.txt"

/-- Curve 175 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve175.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 175. -/
public theorem curve175_j : curve175.j = -174888384183168744821154873481355764026172886087647742729967664496591610904297 / 6527958798095322183341185914059657876076212733528694190329012786061131776 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
