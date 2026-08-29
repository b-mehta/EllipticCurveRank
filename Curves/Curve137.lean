/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 137 has rank at least 11

The elliptic curve recorded as
[curve 137](https://elliptic-rank.icarm.cloud/curve/137) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -41032399`   and
  `a₆ = 106082399089`

over `ℚ`. It has Mordell-Weil rank at least `11`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve137.txt`; descent labels are in
`data/curve137-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 137 over `ℚ`. -/
@[expose] public def curve137 : WeierstrassCurve ℚ := ⟨1, -1, 0, -41032399, 106082399089⟩

/-- ICARM leaderboard curve 137 has Mordell-Weil rank at least `11`. -/
public theorem curve137_hasRankGE_11 : HasRankGE curve137 11 := by
  unfold curve137
  certify_curve torsion 7 "data/curve137.txt" "data/curve137-labels.txt"

/-- Curve 137 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve137.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 137. -/
public theorem curve137_j : curve137.j = -7640195042367733779584638281 / 439152040586971624338548 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
