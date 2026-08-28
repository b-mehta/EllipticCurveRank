/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 127 has rank at least 7

The elliptic curve recorded as
[curve 127](https://elliptic-rank.icarm.cloud/curve/127) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -15577`   and
  `a₆ = 744876`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve127.txt`; descent labels are in
`data/curve127-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 127 over `ℚ`. -/
@[expose] public def curve127 : WeierstrassCurve ℚ := ⟨0, 0, 1, -15577, 744876⟩

/-- ICARM leaderboard curve 127 has Mordell-Weil rank at least `7`. -/
public theorem curve127_hasRankGE_7 : HasRankGE curve127 7 := by
  unfold curve127
  certify_curve torsion 11 "data/curve127.txt" "data/curve127-labels.txt"

/-- Curve 127 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve127.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 127. -/
public theorem curve127_j : curve127.j = 417998931705409536 / 2206378706437 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
