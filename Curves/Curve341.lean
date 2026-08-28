/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 341 has rank at least 19

The elliptic curve recorded as
[curve 341](https://elliptic-rank.icarm.cloud/curve/341) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3084587601676831625566042717`   and
  `a₆ = 65997762542852427586433425766175664366441`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve341.txt`; descent labels are in
`data/curve341-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 341 over `ℚ`. -/
@[expose] public def curve341 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -3084587601676831625566042717, 65997762542852427586433425766175664366441⟩

/-- ICARM leaderboard curve 341 has Mordell-Weil rank at least `19`. -/
public theorem curve341_hasRankGE_19 : HasRankGE curve341 19 := by
  unfold curve341
  certify_curve torsion 13 "data/curve341.txt" "data/curve341-labels.txt"

/-- Curve 341 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve341.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 341. -/
public theorem curve341_j : curve341.j = -207727986730208773733654854439292769558649335493222138905842859100652426737661338913 / 213567174314848126136990816287720757047522090419144194902277884007004708031604 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
