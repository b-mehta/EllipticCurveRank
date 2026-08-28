/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 260 has rank at least 8

The elliptic curve recorded as
[curve 260](https://elliptic-rank.icarm.cloud/curve/260) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -27589`   and
  `a₆ = 1109929`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve260.txt`; descent labels are in
`data/curve260-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 260 over `ℚ`. -/
@[expose] public def curve260 : WeierstrassCurve ℚ := ⟨1, -1, 0, -27589, 1109929⟩

/-- ICARM leaderboard curve 260 has Mordell-Weil rank at least `8`. -/
public theorem curve260_hasRankGE_8 : HasRankGE curve260 8 := by
  unfold curve260
  certify_curve torsion 7 "data/curve260.txt" "data/curve260-labels.txt"

/-- Curve 260 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve260.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 260. -/
public theorem curve260_j : curve260.j = 2322418296423280041 / 818386753539772 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
