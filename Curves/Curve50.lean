/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 50 has rank at least 11

The elliptic curve recorded as
[curve 50](https://elliptic-rank.icarm.cloud/curve/50) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -16359067`   and
  `a₆ = 26274178986`

over `ℚ`. It has Mordell-Weil rank at least `11`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve50.txt`; descent labels are in
`data/curve50-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 50 over `ℚ`. -/
@[expose] public def curve50 : WeierstrassCurve ℚ := ⟨0, 0, 1, -16359067, 26274178986⟩

/-- ICARM leaderboard curve 50 has Mordell-Weil rank at least `11`. -/
public theorem curve50_hasRankGE_11 : HasRankGE curve50 11 := by
  unfold curve50
  certify_curve torsion 17 "data/curve50.txt" "data/curve50-labels.txt"

/-- Curve 50 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve50.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 50. -/
public theorem curve50_j : curve50.j = -484171593245878168582557696 / 18031737725935636520843 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
