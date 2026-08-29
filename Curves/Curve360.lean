/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 360 has rank at least 9

The elliptic curve recorded as
[curve 360](https://elliptic-rank.icarm.cloud/curve/360) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -238158975`   and
  `a₆ = 1544082864921`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve360.txt`; descent labels are in
`data/curve360-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 360 over `ℚ`. -/
@[expose] public def curve360 : WeierstrassCurve ℚ := ⟨1, 0, 0, -238158975, 1544082864921⟩

/-- ICARM leaderboard curve 360 has Mordell-Weil rank at least `9`. -/
public theorem curve360_hasRankGE_9 : HasRankGE curve360 9 := by
  unfold curve360
  certify_curve torsion 29 "data/curve360.txt" "data/curve360-labels.txt"

/-- Curve 360 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve360.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 360. -/
public theorem curve360_j : curve360.j = -1493910465699694940566932812401 / 165465855842698768314820608 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
