/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 244 has rank at least 14

The elliptic curve recorded as
[curve 244](https://elliptic-rank.icarm.cloud/curve/244) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -44788551847`   and
  `a₆ = 2462203786988170`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve244.txt`; descent labels are in
`data/curve244-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 244 over `ℚ`. -/
@[expose] public def curve244 : WeierstrassCurve ℚ := ⟨0, 0, 0, -44788551847, 2462203786988170⟩

/-- ICARM leaderboard curve 244 has Mordell-Weil rank at least `14`. -/
public theorem curve244_hasRankGE_14 : HasRankGE curve244 14 := by
  unfold curve244
  certify_curve torsion 13 "data/curve244.txt" "data/curve244-labels.txt"

/-- Curve 244 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve244.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 244. -/
public theorem curve244_j : curve244.j = 38813678889120033899103288744086736 / 12231239590388150121299598016837 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
