/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 366 has rank at least 9

The elliptic curve recorded as
[curve 366](https://elliptic-rank.icarm.cloud/curve/366) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -19968242`   and
  `a₆ = 24608110065`

over `ℚ`. It has Mordell-Weil rank at least `9`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve366.txt`; descent labels are in
`data/curve366-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 366 over `ℚ`. -/
@[expose] public def curve366 : WeierstrassCurve ℚ := ⟨1, -1, 1, -19968242, 24608110065⟩

/-- ICARM leaderboard curve 366 has Mordell-Weil rank at least `9`. -/
public theorem curve366_hasRankGE_9 : HasRankGE curve366 9 := by
  unfold curve366
  certify_curve torsion 17 "data/curve366.txt" "data/curve366-labels.txt"

/-- Curve 366 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve366.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 366. -/
public theorem curve366_j : curve366.j = 3623572142486706104845707 / 1020861880720814111744 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
