/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 254 has rank at least 7

The elliptic curve recorded as
[curve 254](https://elliptic-rank.icarm.cloud/curve/254) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 72351`   and
  `a₆ = 71289`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve254.txt`; descent labels are in
`data/curve254-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 254 over `ℚ`. -/
@[expose] public def curve254 : WeierstrassCurve ℚ := ⟨0, 0, 0, 72351, 71289⟩

/-- ICARM leaderboard curve 254 has Mordell-Weil rank at least `7`. -/
public theorem curve254_hasRankGE_7 : HasRankGE curve254 7 := by
  unfold curve254
  certify_curve torsion 5 "data/curve254.txt" "data/curve254-labels.txt"

/-- Curve 254 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve254.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 254. -/
public theorem curve254_j : curve254.j = 3590953781660928 / 2078286479999 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
