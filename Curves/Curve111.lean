/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 111 has rank at least 5

The elliptic curve recorded as
[curve 111](https://elliptic-rank.icarm.cloud/curve/111) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -139`   and
  `a₆ = 732`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve111.txt`; descent labels are in
`data/curve111-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 111 over `ℚ`. -/
@[expose] public def curve111 : WeierstrassCurve ℚ := ⟨0, 0, 1, -139, 732⟩

/-- ICARM leaderboard curve 111 has Mordell-Weil rank at least `5`. -/
public theorem curve111_hasRankGE_5 : HasRankGE curve111 5 := by
  unfold curve111
  certify_curve torsion 5 "data/curve111.txt" "data/curve111-labels.txt"

/-- Curve 111 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve111.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 111. -/
public theorem curve111_j : curve111.j = -297007976448 / 59754491 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
