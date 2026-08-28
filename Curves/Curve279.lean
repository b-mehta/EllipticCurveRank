/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 279 has rank at least 6

The elliptic curve recorded as
[curve 279](https://elliptic-rank.icarm.cloud/curve/279) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -2010516977329`   and
  `a₆ = 71337059553120256`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve279.txt`; descent labels are in
`data/curve279-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 279 over `ℚ`. -/
@[expose] public def curve279 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2010516977329, 71337059553120256⟩

/-- ICARM leaderboard curve 279 has Mordell-Weil rank at least `6`. -/
public theorem curve279_hasRankGE_6 : HasRankGE curve279 6 := by
  unfold curve279
  certify_curve torsion 5 "data/curve279.txt" "data/curve279-labels.txt"

/-- Curve 279 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve279.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 279. -/
public theorem curve279_j : curve279.j = 806327953815992502171886272 / 464652646250619140289361 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
