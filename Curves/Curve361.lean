/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 361 has rank at least 8

The elliptic curve recorded as
[curve 361](https://elliptic-rank.icarm.cloud/curve/361) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -435052160`   and
  `a₆ = 3407298580001`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve361.txt`; descent labels are in
`data/curve361-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 361 over `ℚ`. -/
@[expose] public def curve361 : WeierstrassCurve ℚ := ⟨1, 1, 1, -435052160, 3407298580001⟩

/-- ICARM leaderboard curve 361 has Mordell-Weil rank at least `8`. -/
public theorem curve361_hasRankGE_8 : HasRankGE curve361 8 := by
  unfold curve361
  certify_curve torsion 13 "data/curve361.txt" "data/curve361-labels.txt"

/-- Curve 361 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve361.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 361. -/
public theorem curve361_j : curve361.j = 9106420487134731277452124170241 / 254002281318218462945513472 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
