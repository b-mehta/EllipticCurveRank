/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 334 has rank at least 19

The elliptic curve recorded as
[curve 334](https://elliptic-rank.icarm.cloud/curve/334) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -20088058719108362343982670142`   and
  `a₆ = 1058707069906879133804800274913812097605016`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve334.txt`; descent labels are in
`data/curve334-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 334 over `ℚ`. -/
@[expose] public def curve334 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -20088058719108362343982670142, 1058707069906879133804800274913812097605016⟩

/-- ICARM leaderboard curve 334 has Mordell-Weil rank at least `19`. -/
public theorem curve334_hasRankGE_19 : HasRankGE curve334 19 := by
  unfold curve334
  certify_curve torsion 7 "data/curve334.txt" "data/curve334-labels.txt"

/-- Curve 334 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve334.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 334. -/
public theorem curve334_j : curve334.j = 78702778593592076827659186225195803873899913858909584814747237964912717344987970073 / 3035911104339933372549931721047277087933143586375526582139695565059034404278316 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
