/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 234 has rank at least 19

The elliptic curve recorded as
[curve 234](https://elliptic-rank.icarm.cloud/curve/234) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -2770478907376168032636869`   and
  `a₆ = 1775138479573443551078307813696866276`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by RoyManami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 234 over `ℚ`. -/
@[expose] public def curve234 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -2770478907376168032636869, 1775138479573443551078307813696866276⟩

/-- ICARM leaderboard curve 234 has Mordell-Weil rank at least `19`. -/
public theorem curve234_hasRankGE_19 : HasRankGE curve234 19 := by
  unfold curve234
  certify_curve torsion 13 "data/curve234.txt" "data/curve234-labels.txt"

/-- Curve 234 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve234.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 234. -/
public theorem curve234_j : curve234.j = -2351734316006072914007028216025104616202076075008992913181137205785940920829769 / 325021758664267435353269545802736616838357964735913965003055852319441700 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
