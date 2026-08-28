/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 358 has rank at least 9

The elliptic curve recorded as
[curve 358](https://elliptic-rank.icarm.cloud/curve/358) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -71192370`   and
  `a₆ = 226048177800`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve358.txt`; descent labels are in
`data/curve358-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 358 over `ℚ`. -/
@[expose] public def curve358 : WeierstrassCurve ℚ := ⟨1, 1, 0, -71192370, 226048177800⟩

/-- ICARM leaderboard curve 358 has Mordell-Weil rank at least `9`. -/
public theorem curve358_hasRankGE_9 : HasRankGE curve358 9 := by
  unfold curve358
  certify_curve torsion 7 "data/curve358.txt" "data/curve358-labels.txt"

/-- Curve 358 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve358.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 358. -/
public theorem curve358_j : curve358.j = 319237617731321174810360093 / 8103717992314006005996 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
