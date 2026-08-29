/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 114 has rank at least 6

The elliptic curve recorded as
[curve 114](https://elliptic-rank.icarm.cloud/curve/114) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -16249`   and
  `a₆ = 799549`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve114.txt`; descent labels are in
`data/curve114-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 114 over `ℚ`. -/
@[expose] public def curve114 : WeierstrassCurve ℚ := ⟨1, -1, 0, -16249, 799549⟩

/-- ICARM leaderboard curve 114 has Mordell-Weil rank at least `6`. -/
public theorem curve114_hasRankGE_6 : HasRankGE curve114 6 := by
  unfold curve114
  certify_curve torsion 7 "data/curve114.txt" "data/curve114-labels.txt"

/-- Curve 114 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve114.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 114. -/
public theorem curve114_j : curve114.j = 474480820759080681 / 1214588595952 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
