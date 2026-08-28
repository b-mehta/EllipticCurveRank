/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 283 has rank at least 7

The elliptic curve recorded as
[curve 283](https://elliptic-rank.icarm.cloud/curve/283) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1027782`   and
  `a₆ = 318095064`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve283.txt`; descent labels are in
`data/curve283-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 283 over `ℚ`. -/
@[expose] public def curve283 : WeierstrassCurve ℚ := ⟨1, 1, 0, -1027782, 318095064⟩

/-- ICARM leaderboard curve 283 has Mordell-Weil rank at least `7`. -/
public theorem curve283_hasRankGE_7 : HasRankGE curve283 7 := by
  unfold curve283
  certify_curve torsion 17 "data/curve283.txt" "data/curve283-labels.txt"

/-- Curve 283 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve283.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 283. -/
public theorem curve283_j : curve283.j = 120068032648263756837481 / 25654349339596687500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
