/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 112 has rank at least 6

The elliptic curve recorded as
[curve 112](https://elliptic-rank.icarm.cloud/curve/112) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -7077`   and
  `a₆ = 235516`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve112.txt`; descent labels are in
`data/curve112-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 112 over `ℚ`. -/
@[expose] public def curve112 : WeierstrassCurve ℚ := ⟨0, 0, 1, -7077, 235516⟩

/-- ICARM leaderboard curve 112 has Mordell-Weil rank at least `6`. -/
public theorem curve112_hasRankGE_6 : HasRankGE curve112 6 := by
  unfold curve112
  certify_curve torsion 7 "data/curve112.txt" "data/curve112-labels.txt"

/-- Curve 112 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve112.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 112. -/
public theorem curve112_j : curve112.j = -53770462326784 / 1752703347 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
