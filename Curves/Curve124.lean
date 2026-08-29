/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 124 has rank at least 7

The elliptic curve recorded as
[curve 124](https://elliptic-rank.icarm.cloud/curve/124) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -5707`   and
  `a₆ = 151416`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve124.txt`; descent labels are in
`data/curve124-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 124 over `ℚ`. -/
@[expose] public def curve124 : WeierstrassCurve ℚ := ⟨0, 0, 1, -5707, 151416⟩

/-- ICARM leaderboard curve 124 has Mordell-Weil rank at least `7`. -/
public theorem curve124_hasRankGE_7 : HasRankGE curve124 7 := by
  unfold curve124
  certify_curve torsion 11 "data/curve124.txt" "data/curve124-labels.txt"

/-- Curve 124 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve124.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 124. -/
public theorem curve124_j : curve124.j = 20556412774649856 / 1991659717477 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
