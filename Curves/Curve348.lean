/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 348 has rank at least 8

The elliptic curve recorded as
[curve 348](https://elliptic-rank.icarm.cloud/curve/348) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -25465228`   and
  `a₆ = 50335019942`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve348.txt`; descent labels are in
`data/curve348-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 348 over `ℚ`. -/
@[expose] public def curve348 : WeierstrassCurve ℚ := ⟨1, 0, 1, -25465228, 50335019942⟩

/-- ICARM leaderboard curve 348 has Mordell-Weil rank at least `8`. -/
public theorem curve348_hasRankGE_8 : HasRankGE curve348 8 := by
  unfold curve348
  certify_curve torsion 11 "data/curve348.txt" "data/curve348-labels.txt"

/-- Curve 348 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve348.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 348. -/
public theorem curve348_j : curve348.j = -760631373010768489273561 / 15718865802632635788 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
