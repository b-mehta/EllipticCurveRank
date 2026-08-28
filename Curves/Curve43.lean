/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 43 has rank at least 6

The elliptic curve recorded as
[curve 43](https://elliptic-rank.icarm.cloud/curve/43) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2582`   and
  `a₆ = 48720`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve43.txt`; descent labels are in
`data/curve43-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 43 over `ℚ`. -/
@[expose] public def curve43 : WeierstrassCurve ℚ := ⟨1, 1, 0, -2582, 48720⟩

/-- ICARM leaderboard curve 43 has Mordell-Weil rank at least `6`. -/
public theorem curve43_hasRankGE_6 : HasRankGE curve43 6 := by
  unfold curve43
  certify_curve torsion 17 "data/curve43.txt" "data/curve43-labels.txt"

/-- Curve 43 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve43.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 43. -/
public theorem curve43_j : curve43.j = 1904825573752681 / 31125382452 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
