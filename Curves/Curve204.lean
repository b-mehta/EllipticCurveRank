/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 204 has rank at least 14

The elliptic curve recorded as
[curve 204](https://elliptic-rank.icarm.cloud/curve/204) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -40816112666798768214524743126`   and
  `a₆ = 3175238037154846187302797412986141032805156`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve204.txt`; descent labels are in
`data/curve204-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 204 over `ℚ`. -/
@[expose] public def curve204 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -40816112666798768214524743126, 3175238037154846187302797412986141032805156⟩

/-- ICARM leaderboard curve 204 has Mordell-Weil rank at least `14`. -/
public theorem curve204_hasRankGE_14 : HasRankGE curve204 14 := by
  unfold curve204
  certify_curve torsion 41 "data/curve204.txt" "data/curve204-labels.txt"

/-- Curve 204 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve204.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 204. -/
public theorem curve204_j : curve204.j = -7520013709562129764708714994151769138096180608144695314867579253066902213707629891087127649 / 3623222374799711246641358701859136275557470213922538013251076487946923600073999257600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
