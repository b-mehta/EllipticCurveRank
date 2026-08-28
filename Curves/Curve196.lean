/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 196 has rank at least 14

The elliptic curve recorded as
[curve 196](https://elliptic-rank.icarm.cloud/curve/196) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -585078982552785047`   and
  `a₆ = 179426017231461870343844271`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve196.txt`; descent labels are in
`data/curve196-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 196 over `ℚ`. -/
@[expose] public def curve196 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -585078982552785047, 179426017231461870343844271⟩

/-- ICARM leaderboard curve 196 has Mordell-Weil rank at least `14`. -/
public theorem curve196_hasRankGE_14 : HasRankGE curve196 14 := by
  unfold curve196
  certify_curve torsion 29 "data/curve196.txt" "data/curve196-labels.txt"

/-- Curve 196 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve196.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 196. -/
public theorem curve196_j : curve196.j = -30383631225134026329161820752713557105453336352379998249 / 1494625622969308830571287148924177802650500096000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
