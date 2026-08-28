/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 123 has rank at least 7

The elliptic curve recorded as
[curve 123](https://elliptic-rank.icarm.cloud/curve/123) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -18664`   and
  `a₆ = 958204`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve123.txt`; descent labels are in
`data/curve123-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 123 over `ℚ`. -/
@[expose] public def curve123 : WeierstrassCurve ℚ := ⟨1, -1, 0, -18664, 958204⟩

/-- ICARM leaderboard curve 123 has Mordell-Weil rank at least `7`. -/
public theorem curve123_hasRankGE_7 : HasRankGE curve123 7 := by
  unfold curve123
  certify_curve torsion 7 "data/curve123.txt" "data/curve123-labels.txt"

/-- Curve 123 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve123.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 123. -/
public theorem curve123_j : curve123.j = 719036568751082841 / 23319753244372 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
