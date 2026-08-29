/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 101 has rank at least 10

The elliptic curve recorded as
[curve 101](https://elliptic-rank.icarm.cloud/curve/101) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4513546`   and
  `a₆ = 3716615296`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve101.txt`; descent labels are in
`data/curve101-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 101 over `ℚ`. -/
@[expose] public def curve101 : WeierstrassCurve ℚ := ⟨1, -1, 0, -4513546, 3716615296⟩

/-- ICARM leaderboard curve 101 has Mordell-Weil rank at least `10`. -/
public theorem curve101_hasRankGE_10 : HasRankGE curve101 10 := by
  unfold curve101
  certify_curve torsion 5 "data/curve101.txt" "data/curve101-labels.txt"

/-- Curve 101 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve101.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 101. -/
public theorem curve101_j : curve101.j = -10168979810787453005768313 / 78865885564446731516 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
