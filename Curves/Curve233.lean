/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 233 has rank at least 18

The elliptic curve recorded as
[curve 233](https://elliptic-rank.icarm.cloud/curve/233) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -47059713436231131280063000`   and
  `a₆ = 124291234348538980027099166608538874432`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve233.txt`; descent labels are in
`data/curve233-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 233 over `ℚ`. -/
@[expose] public def curve233 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -47059713436231131280063000, 124291234348538980027099166608538874432⟩

/-- ICARM leaderboard curve 233 has Mordell-Weil rank at least `18`. -/
public theorem curve233_hasRankGE_18 : HasRankGE curve233 18 := by
  unfold curve233
  certify_curve torsion 13 "data/curve233.txt" "data/curve233-labels.txt"

/-- Curve 233 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve233.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 233. -/
public theorem curve233_j : curve233.j = -11525812411511073313303361057840326200655290972710278774140494201864955522057072001 / 3639993566490641216689747626786054555892020902459466267407640882904268800000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
