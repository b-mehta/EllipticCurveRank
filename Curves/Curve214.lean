/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 214 has rank at least 14

The elliptic curve recorded as
[curve 214](https://elliptic-rank.icarm.cloud/curve/214) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -579129722683962784448`   and
  `a₆ = -1024153228236700825546996771869`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve214.txt`; descent labels are in
`data/curve214-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 214 over `ℚ`. -/
@[expose] public def curve214 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -579129722683962784448, -1024153228236700825546996771869⟩

/-- ICARM leaderboard curve 214 has Mordell-Weil rank at least `14`. -/
public theorem curve214_hasRankGE_14 : HasRankGE curve214 14 := by
  unfold curve214
  certify_curve torsion 19 "data/curve214.txt" "data/curve214-labels.txt"

/-- Curve 214 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve214.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 214. -/
public theorem curve214_j : curve214.j = 88398521830631281710641344242354969659174695744616517696715543083 / 49291858944955980588687396557259333093543848448540275651379200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
