/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 368 has rank at least 8

The elliptic curve recorded as
[curve 368](https://elliptic-rank.icarm.cloud/curve/368) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -10380258`   and
  `a₆ = 13686541281`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve368.txt`; descent labels are in
`data/curve368-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 368 over `ℚ`. -/
@[expose] public def curve368 : WeierstrassCurve ℚ := ⟨1, -1, 1, -10380258, 13686541281⟩

/-- ICARM leaderboard curve 368 has Mordell-Weil rank at least `8`. -/
public theorem curve368_hasRankGE_8 : HasRankGE curve368 8 := by
  unfold curve368
  certify_curve torsion 17 "data/curve368.txt" "data/curve368-labels.txt"

/-- Curve 368 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve368.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 368. -/
public theorem curve368_j : curve368.j = -123693852733528978449959409 / 9310075214010352870400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
