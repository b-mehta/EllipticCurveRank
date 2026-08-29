/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 236 has rank at least 16

The elliptic curve recorded as
[curve 236](https://elliptic-rank.icarm.cloud/curve/236) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -40169264421361745502396`   and
  `a₆ = 2062092485931366276599688546201504`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve236.txt`; descent labels are in
`data/curve236-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 236 over `ℚ`. -/
@[expose] public def curve236 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -40169264421361745502396, 2062092485931366276599688546201504⟩

/-- ICARM leaderboard curve 236 has Mordell-Weil rank at least `16`. -/
public theorem curve236_hasRankGE_16 : HasRankGE curve236 16 := by
  unfold curve236
  certify_curve torsion 23 "data/curve236.txt" "data/curve236-labels.txt"

/-- Curve 236 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve236.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 236. -/
public theorem curve236_j : curve236.j = 2400589337976219717779823855971704947632156800004651566965805147968 / 774035290996857182542614883358544393793840190308901167574688763 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
