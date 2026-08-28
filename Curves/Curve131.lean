/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 131 has rank at least 8

The elliptic curve recorded as
[curve 131](https://elliptic-rank.icarm.cloud/curve/131) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -124294`   and
  `a₆ = 14418784`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve131.txt`; descent labels are in
`data/curve131-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 131 over `ℚ`. -/
@[expose] public def curve131 : WeierstrassCurve ℚ := ⟨1, -1, 0, -124294, 14418784⟩

/-- ICARM leaderboard curve 131 has Mordell-Weil rank at least `8`. -/
public theorem curve131_hasRankGE_8 : HasRankGE curve131 8 := by
  unfold curve131
  certify_curve torsion 7 "data/curve131.txt" "data/curve131-labels.txt"

/-- Curve 131 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve131.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 131. -/
public theorem curve131_j : curve131.j = 212361689273674389561 / 33467812293376612 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
