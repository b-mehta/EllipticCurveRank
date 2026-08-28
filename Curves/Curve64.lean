/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 64 has rank at least 16

The elliptic curve recorded as
[curve 64](https://elliptic-rank.icarm.cloud/curve/64) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 18128458663461957134862581373`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve64.txt`; descent labels are in
`data/curve64-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 64 over `ℚ`. -/
@[expose] public def curve64 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 18128458663461957134862581373⟩

/-- ICARM leaderboard curve 64 has Mordell-Weil rank at least `16`. -/
public theorem curve64_hasRankGE_16 : HasRankGE curve64 16 := by
  unfold curve64
  certify_curve torsion 7 "data/curve64.txt" "data/curve64-labels.txt"

/-- Curve 64 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve64.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 64. -/
public theorem curve64_j : curve64.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
