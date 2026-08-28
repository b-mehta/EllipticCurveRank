/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 194 has rank at least 15

The elliptic curve recorded as
[curve 194](https://elliptic-rank.icarm.cloud/curve/194) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -11524988157418506896`   and
  `a₆ = 15103590903163497035477292096`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve194.txt`; descent labels are in
`data/curve194-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 194 over `ℚ`. -/
@[expose] public def curve194 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -11524988157418506896, 15103590903163497035477292096⟩

/-- ICARM leaderboard curve 194 has Mordell-Weil rank at least `15`. -/
public theorem curve194_hasRankGE_15 : HasRankGE curve194 15 := by
  unfold curve194
  certify_curve torsion 19 "data/curve194.txt" "data/curve194-labels.txt"

/-- Curve 194 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve194.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 194. -/
public theorem curve194_j : curve194.j = -41331886446644560560628478627624512440029888671155256842769 / 140452855156848326269838401454147799491012772352796550 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
