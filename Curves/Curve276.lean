/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 276 has rank at least 15

The elliptic curve recorded as
[curve 276](https://elliptic-rank.icarm.cloud/curve/276) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -3173985189420763`   and
  `a₆ = 71466484807091261962138`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve276.txt`; descent labels are in
`data/curve276-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 276 over `ℚ`. -/
@[expose] public def curve276 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -3173985189420763, 71466484807091261962138⟩

/-- ICARM leaderboard curve 276 has Mordell-Weil rank at least `15`. -/
public theorem curve276_hasRankGE_15 : HasRankGE curve276 15 := by
  unfold curve276
  certify_curve torsion 13 "data/curve276.txt" "data/curve276-labels.txt"

/-- Curve 276 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve276.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 276. -/
public theorem curve276_j : curve276.j = -3453332876117980370499248132130505472947214574276 / 156252508350317087848774675150007936648887475 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
