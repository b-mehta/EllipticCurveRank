/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 278 has rank at least 6

The elliptic curve recorded as
[curve 278](https://elliptic-rank.icarm.cloud/curve/278) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -25876904769`   and
  `a₆ = 1776132919332864`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve278.txt`; descent labels are in
`data/curve278-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 278 over `ℚ`. -/
@[expose] public def curve278 : WeierstrassCurve ℚ := ⟨0, 0, 0, -25876904769, 1776132919332864⟩

/-- ICARM leaderboard curve 278 has Mordell-Weil rank at least `6`. -/
public theorem curve278_hasRankGE_6 : HasRankGE curve278 6 := by
  unfold curve278
  certify_curve torsion 5 "data/curve278.txt" "data/curve278-labels.txt"

/-- Curve 278 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve278.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 278. -/
public theorem curve278_j : curve278.j = -69050242017669732020928 / 9146892156452447471 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
