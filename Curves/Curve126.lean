/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 126 has rank at least 7

The elliptic curve recorded as
[curve 126](https://elliptic-rank.icarm.cloud/curve/126) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -14505`   and
  `a₆ = 667472`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve126.txt`; descent labels are in
`data/curve126-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 126 over `ℚ`. -/
@[expose] public def curve126 : WeierstrassCurve ℚ := ⟨1, 0, 1, -14505, 667472⟩

/-- ICARM leaderboard curve 126 has Mordell-Weil rank at least `7`. -/
public theorem curve126_hasRankGE_7 : HasRankGE curve126 7 := by
  unfold curve126
  certify_curve torsion 5 "data/curve126.txt" "data/curve126-labels.txt"

/-- Curve 126 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve126.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 126. -/
public theorem curve126_j : curve126.j = 337468989148050313 / 2132568452204 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
