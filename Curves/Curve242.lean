/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 242 has rank at least 18

The elliptic curve recorded as
[curve 242](https://elliptic-rank.icarm.cloud/curve/242) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -309526258964080213728331769`   and
  `a₆ = 2161609688903376164317636000643138896976`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve242.txt`; descent labels are in
`data/curve242-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 242 over `ℚ`. -/
@[expose] public def curve242 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -309526258964080213728331769, 2161609688903376164317636000643138896976⟩

/-- ICARM leaderboard curve 242 has Mordell-Weil rank at least `18`. -/
public theorem curve242_hasRankGE_18 : HasRankGE curve242 18 := by
  unfold curve242
  certify_curve torsion 7 "data/curve242.txt" "data/curve242-labels.txt"

/-- Curve 242 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve242.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 242. -/
public theorem curve242_j : curve242.j = -3279564738491162848669708951660269120196010917084095089999105521692864950187581407369 / 120648124472674441798657772129443506216935731373216705396040170880065931985481700 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
