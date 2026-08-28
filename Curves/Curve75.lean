/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 75 has rank at least 8

The elliptic curve recorded as
[curve 75](https://elliptic-rank.icarm.cloud/curve/75) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -23846`   and
  `a₆ = 1022562`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve75.txt`; descent labels are in
`data/curve75-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 75 over `ℚ`. -/
@[expose] public def curve75 : WeierstrassCurve ℚ := ⟨0, 1, 1, -23846, 1022562⟩

/-- ICARM leaderboard curve 75 has Mordell-Weil rank at least `8`. -/
public theorem curve75_hasRankGE_8 : HasRankGE curve75 8 := by
  unfold curve75
  certify_curve torsion 5 "data/curve75.txt" "data/curve75-labels.txt"

/-- Curve 75 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve75.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 75. -/
public theorem curve75_j : curve75.j = 1499645274373402624 / 409086620841461 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
