/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 258 has rank at least 8

The elliptic curve recorded as
[curve 258](https://elliptic-rank.icarm.cloud/curve/258) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -10479`   and
  `a₆ = 1611834`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve258.txt`; descent labels are in
`data/curve258-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 258 over `ℚ`. -/
@[expose] public def curve258 : WeierstrassCurve ℚ := ⟨1, -1, 1, -10479, 1611834⟩

/-- ICARM leaderboard curve 258 has Mordell-Weil rank at least `8`. -/
public theorem curve258_hasRankGE_8 : HasRankGE curve258 8 := by
  unfold curve258
  certify_curve torsion 5 "data/curve258.txt" "data/curve258-labels.txt"

/-- Curve 258 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve258.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 258. -/
public theorem curve258_j : curve258.j = -127246070177248833 / 1045057162881491 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
