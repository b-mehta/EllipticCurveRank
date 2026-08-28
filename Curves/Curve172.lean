/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 172 has rank at least 16

The elliptic curve recorded as
[curve 172](https://elliptic-rank.icarm.cloud/curve/172) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -145932228185273125026647`   and
  `a₆ = 22189248867258609149920496015950319`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve172.txt`; descent labels are in
`data/curve172-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 172 over `ℚ`. -/
@[expose] public def curve172 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -145932228185273125026647, 22189248867258609149920496015950319⟩

/-- ICARM leaderboard curve 172 has Mordell-Weil rank at least `16`. -/
public theorem curve172_hasRankGE_16 : HasRankGE curve172 16 := by
  unfold curve172
  certify_curve torsion 29 "data/curve172.txt" "data/curve172-labels.txt"

/-- Curve 172 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve172.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 172. -/
public theorem curve172_j : curve172.j = -471465398336145519801106671112687291524195537436682218961363697645943849 / 18931755394889657373368934304514134170023750935286386725319680000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
