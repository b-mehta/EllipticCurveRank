/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 352 has rank at least 7

The elliptic curve recorded as
[curve 352](https://elliptic-rank.icarm.cloud/curve/352) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -281475`   and
  `a₆ = 65390161`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve352.txt`; descent labels are in
`data/curve352-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 352 over `ℚ`. -/
@[expose] public def curve352 : WeierstrassCurve ℚ := ⟨1, -1, 0, -281475, 65390161⟩

/-- ICARM leaderboard curve 352 has Mordell-Weil rank at least `7`. -/
public theorem curve352_hasRankGE_7 : HasRankGE curve352 7 := by
  unfold curve352
  certify_curve torsion 7 "data/curve352.txt" "data/curve352-labels.txt"

/-- Curve 352 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve352.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 352. -/
public theorem curve352_j : curve352.j = -3383113242536823601 / 570579987902700 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
