/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 266 has rank at least 7

The elliptic curve recorded as
[curve 266](https://elliptic-rank.icarm.cloud/curve/266) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -42484`   and
  `a₆ = 47524`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve266.txt`; descent labels are in
`data/curve266-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 266 over `ℚ`. -/
@[expose] public def curve266 : WeierstrassCurve ℚ := ⟨0, 0, 0, -42484, 47524⟩

/-- ICARM leaderboard curve 266 has Mordell-Weil rank at least `7`. -/
public theorem curve266_hasRankGE_7 : HasRankGE curve266 7 := by
  unfold curve266
  certify_curve torsion 5 "data/curve266.txt" "data/curve266-labels.txt"

/-- Curve 266 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve266.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 266. -/
public theorem curve266_j : curve266.j = 33125309698710528 / 19165928138629 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
