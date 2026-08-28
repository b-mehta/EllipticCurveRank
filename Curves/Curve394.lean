/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 394 has rank at least 21

The elliptic curve recorded as
[curve 394](https://elliptic-rank.icarm.cloud/curve/394) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -354803089674674467206754048738095`   and
  `a₆ = 2558194545892203175112161719607326368645810580537`

over `ℚ`. It has Mordell-Weil rank at least `21`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve394.txt`; descent labels are in
`data/curve394-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 394 over `ℚ`. -/
@[expose] public def curve394 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -354803089674674467206754048738095, 2558194545892203175112161719607326368645810580537⟩

/-- ICARM leaderboard curve 394 has Mordell-Weil rank at least `21`. -/
public theorem curve394_hasRankGE_21 : HasRankGE curve394 21 := by
  unfold curve394
  certify_curve torsion 19 "data/curve394.txt" "data/curve394-labels.txt"

/-- Curve 394 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve394.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 394. -/
public theorem curve394_j : curve394.j = 4939533001552835478746742830549596923006009694553314320051128402179625733447700310981388073820207322481 / 31362810004008297563332830974145357962340308661810559854716023966067971553607881810277592152000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
