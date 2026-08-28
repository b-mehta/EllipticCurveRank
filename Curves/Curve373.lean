/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 373 has rank at least 7

The elliptic curve recorded as
[curve 373](https://elliptic-rank.icarm.cloud/curve/373) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -22215005`   and
  `a₆ = 40008831921`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve373.txt`; descent labels are in
`data/curve373-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 373 over `ℚ`. -/
@[expose] public def curve373 : WeierstrassCurve ℚ := ⟨1, 0, 0, -22215005, 40008831921⟩

/-- ICARM leaderboard curve 373 has Mordell-Weil rank at least `7`. -/
public theorem curve373_hasRankGE_7 : HasRankGE curve373 7 := by
  unfold curve373
  certify_curve torsion 7 "data/curve373.txt" "data/curve373-labels.txt"

/-- Curve 373 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve373.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 373. -/
public theorem curve373_j : curve373.j = 1212447547346875354009757521 / 10078626487682956050432 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
