/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 262 has rank at least 20

The elliptic curve recorded as
[curve 262](https://elliptic-rank.icarm.cloud/curve/262) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -21065871080015087031831279377`   and
  `a₆ = 1192838816489664881520195774886398643920001`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve262.txt`; descent labels are in
`data/curve262-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 262 over `ℚ`. -/
@[expose] public def curve262 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -21065871080015087031831279377, 1192838816489664881520195774886398643920001⟩

/-- ICARM leaderboard curve 262 has Mordell-Weil rank at least `20`. -/
public theorem curve262_hasRankGE_20 : HasRankGE curve262 20 := by
  unfold curve262
  certify_curve torsion 7 "data/curve262.txt" "data/curve262-labels.txt"

/-- Curve 262 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve262.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 262. -/
public theorem curve262_j : curve262.j = -1418190101863994522925038975369701783356701907835947019149306087828734536568916038070729 / 22467064161715375330421234795475784023640594542045766381615117473299107266656000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
