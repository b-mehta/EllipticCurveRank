/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 105 has rank at least 12

The elliptic curve recorded as
[curve 105](https://elliptic-rank.icarm.cloud/curve/105) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -46496231372`   and
  `a₆ = 3827433258938575`

over `ℚ`. It has Mordell-Weil rank at least `12`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve105.txt`; descent labels are in
`data/curve105-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 105 over `ℚ`. -/
@[expose] public def curve105 : WeierstrassCurve ℚ := ⟨1, -1, 1, -46496231372, 3827433258938575⟩

/-- ICARM leaderboard curve 105 has Mordell-Weil rank at least `12`. -/
public theorem curve105_hasRankGE_12 : HasRankGE curve105 12 := by
  unfold curve105
  certify_curve torsion 13 "data/curve105.txt" "data/curve105-labels.txt"

/-- Curve 105 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve105.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 105. -/
public theorem curve105_j : curve105.j = 15249283729104197687755615853059449 / 143835419585315582345839863808 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
