/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 218 has rank at least 15

The elliptic curve recorded as
[curve 218](https://elliptic-rank.icarm.cloud/curve/218) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -774334321896533858`   and
  `a₆ = 184415786422239825540685056`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve218.txt`; descent labels are in
`data/curve218-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 218 over `ℚ`. -/
@[expose] public def curve218 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -774334321896533858, 184415786422239825540685056⟩

/-- ICARM leaderboard curve 218 has Mordell-Weil rank at least `15`. -/
public theorem curve218_hasRankGE_15 : HasRankGE curve218 15 := by
  unfold curve218
  certify_curve torsion 13 "data/curve218.txt" "data/curve218-labels.txt"

/-- Curve 218 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve218.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 218. -/
public theorem curve218_j : curve218.j = 436436436017558033800569097982275426550011944850994569 / 127687725043026889391313482105751002878034587362500 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
