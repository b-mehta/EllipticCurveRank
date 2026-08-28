/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 371 has rank at least 10

The elliptic curve recorded as
[curve 371](https://elliptic-rank.icarm.cloud/curve/371) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -851586267`   and
  `a₆ = 7403133843290`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve371.txt`; descent labels are in
`data/curve371-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 371 over `ℚ`. -/
@[expose] public def curve371 : WeierstrassCurve ℚ := ⟨0, 0, 0, -851586267, 7403133843290⟩

/-- ICARM leaderboard curve 371 has Mordell-Weil rank at least `10`. -/
public theorem curve371_hasRankGE_10 : HasRankGE curve371 10 := by
  unfold curve371
  certify_curve torsion 7 "data/curve371.txt" "data/curve371-labels.txt"

/-- Curve 371 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve371.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 371. -/
public theorem curve371_j : curve371.j = 91491800612380920645643876 / 21229982587219418036817 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
