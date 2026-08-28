/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 245 has rank at least 20

The elliptic curve recorded as
[curve 245](https://elliptic-rank.icarm.cloud/curve/245) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -25880411472355347134118026792`   and
  `a₆ = 1606663697747901005185875883284420820193259`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve245.txt`; descent labels are in
`data/curve245-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 245 over `ℚ`. -/
@[expose] public def curve245 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -25880411472355347134118026792, 1606663697747901005185875883284420820193259⟩

/-- ICARM leaderboard curve 245 has Mordell-Weil rank at least `20`. -/
public theorem curve245_hasRankGE_20 : HasRankGE curve245 20 := by
  unfold curve245
  certify_curve torsion 7 "data/curve245.txt" "data/curve245-labels.txt"

/-- Curve 245 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve245.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 245. -/
public theorem curve245_j : curve245.j = -2629721242145377367360328028212393680003509529208561360391440626809483911772440815341369 / 7870273853832723941717869848875068608660266422531817530626444192767266104360960000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
