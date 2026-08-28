/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 224 has rank at least 18

The elliptic curve recorded as
[curve 224](https://elliptic-rank.icarm.cloud/curve/224) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -6673066689650959455557789303`   and
  `a₆ = 209378639414088313855940823602467379072006`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve224.txt`; descent labels are in
`data/curve224-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 224 over `ℚ`. -/
@[expose] public def curve224 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -6673066689650959455557789303, 209378639414088313855940823602467379072006⟩

/-- ICARM leaderboard curve 224 has Mordell-Weil rank at least `18`. -/
public theorem curve224_hasRankGE_18 : HasRankGE curve224 18 := by
  unfold curve224
  certify_curve torsion 37 "data/curve224.txt" "data/curve224-labels.txt"

/-- Curve 224 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve224.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 224. -/
public theorem curve224_j : curve224.j = 32862462805525651512016592070227750677188884080703242612724510489987982074941944058598761 / 79001812652238926310614069141452885179698753918710242185753213892099337491708562500 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
