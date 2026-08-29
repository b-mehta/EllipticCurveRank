/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 216 has rank at least 17

The elliptic curve recorded as
[curve 216](https://elliptic-rank.icarm.cloud/curve/216) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -292164008972198360516541`   and
  `a₆ = 60777760375298123458072491954931825`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve216.txt`; descent labels are in
`data/curve216-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 216 over `ℚ`. -/
@[expose] public def curve216 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -292164008972198360516541, 60777760375298123458072491954931825⟩

/-- ICARM leaderboard curve 216 has Mordell-Weil rank at least `17`. -/
public theorem curve216_hasRankGE_17 : HasRankGE curve216 17 := by
  unfold curve216
  certify_curve torsion 7 "data/curve216.txt" "data/curve216-labels.txt"

/-- Curve 216 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve216.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 216. -/
public theorem curve216_j : curve216.j = 2758060938339783329634378370828800350316489297273603400311579889539173072209 / 319660562013917792358156721464086339946753006672777251625449427814400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
