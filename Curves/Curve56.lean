/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 56 has rank at least 6

The elliptic curve recorded as
[curve 56](https://elliptic-rank.icarm.cloud/curve/56) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -277`   and
  `a₆ = 4566`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve56.txt`; descent labels are in
`data/curve56-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 56 over `ℚ`. -/
@[expose] public def curve56 : WeierstrassCurve ℚ := ⟨0, 0, 1, -277, 4566⟩

/-- ICARM leaderboard curve 56 has Mordell-Weil rank at least `6`. -/
public theorem curve56_hasRankGE_6 : HasRankGE curve56 6 := by
  unfold curve56
  certify_curve torsion 17 "data/curve56.txt" "data/curve56-labels.txt"

/-- Curve 56 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve56.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 56. -/
public theorem curve56_j : curve56.j = -2350514958336 / 7647224363 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
