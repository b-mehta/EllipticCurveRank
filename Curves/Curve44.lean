/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 44 has rank at least 7

The elliptic curve recorded as
[curve 44](https://elliptic-rank.icarm.cloud/curve/44) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -10012`   and
  `a₆ = 346900`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve44.txt`; descent labels are in
`data/curve44-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 44 over `ℚ`. -/
@[expose] public def curve44 : WeierstrassCurve ℚ := ⟨0, 0, 0, -10012, 346900⟩

/-- ICARM leaderboard curve 44 has Mordell-Weil rank at least `7`. -/
public theorem curve44_hasRankGE_7 : HasRankGE curve44 7 := by
  unfold curve44
  certify_curve torsion 23 "data/curve44.txt" "data/curve44-labels.txt"

/-- Curve 44 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve44.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 44. -/
public theorem curve44_j : curve44.j = 433557066986496 / 47827988557 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
