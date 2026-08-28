/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 95 has rank at least 10

The elliptic curve recorded as
[curve 95](https://elliptic-rank.icarm.cloud/curve/95) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -9581420`   and
  `a₆ = 11213539236`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve95.txt`; descent labels are in
`data/curve95-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 95 over `ℚ`. -/
@[expose] public def curve95 : WeierstrassCurve ℚ := ⟨0, -1, 0, -9581420, 11213539236⟩

/-- ICARM leaderboard curve 95 has Mordell-Weil rank at least `10`. -/
public theorem curve95_hasRankGE_10 : HasRankGE curve95 10 := by
  unfold curve95
  certify_curve torsion 7 "data/curve95.txt" "data/curve95-labels.txt"

/-- Curve 95 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve95.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 95. -/
public theorem curve95_j : curve95.j = 379991100623822653625296 / 7831019469860607357 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
