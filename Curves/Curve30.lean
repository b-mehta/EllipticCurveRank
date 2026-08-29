/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 30 has rank at least 9

The elliptic curve recorded as
[curve 30](https://elliptic-rank.icarm.cloud/curve/30) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1608154463`   and
  `a₆ = 25555312501831`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve30.txt`; descent labels are in
`data/curve30-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 30 over `ℚ`. -/
@[expose] public def curve30 : WeierstrassCurve ℚ := ⟨1, -1, 1, -1608154463, 25555312501831⟩

/-- ICARM leaderboard curve 30 has Mordell-Weil rank at least `9`. -/
public theorem curve30_hasRankGE_9 : HasRankGE curve30 9 := by
  unfold curve30
  certify_curve torsion 7 "data/curve30.txt" "data/curve30-labels.txt"

/-- Curve 30 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve30.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 30. -/
public theorem curve30_j : curve30.j = -630927510631066796771741791401 / 21874549145075356208537600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
