/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 293 has rank at least 19

The elliptic curve recorded as
[curve 293](https://elliptic-rank.icarm.cloud/curve/293) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -5903488565485287740438969673369`   and
  `a₆ = 5518803574595815094969270147112053094136508125`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve293.txt`; descent labels are in
`data/curve293-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 293 over `ℚ`. -/
@[expose] public def curve293 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -5903488565485287740438969673369, 5518803574595815094969270147112053094136508125⟩

/-- ICARM leaderboard curve 293 has Mordell-Weil rank at least `19`. -/
public theorem curve293_hasRankGE_19 : HasRankGE curve293 19 := by
  unfold curve293
  certify_curve torsion 17 "data/curve293.txt" "data/curve293-labels.txt"

/-- Curve 293 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve293.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 293. -/
public theorem curve293_j : curve293.j = 31212054959849262750890189941956898271232311606133481883038681381565385424051983230975245784209 / 13824904744453640171252956772248533246940982311314493031808917593179782924138986166490000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
