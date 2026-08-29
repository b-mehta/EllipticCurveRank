/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 198 has rank at least 14

The elliptic curve recorded as
[curve 198](https://elliptic-rank.icarm.cloud/curve/198) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1519707018181529074677`   and
  `a₆ = 22869247242133051599466107911241`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve198.txt`; descent labels are in
`data/curve198-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 198 over `ℚ`. -/
@[expose] public def curve198 : WeierstrassCurve ℚ :=
  ⟨1, 1, 0, -1519707018181529074677, 22869247242133051599466107911241⟩

/-- ICARM leaderboard curve 198 has Mordell-Weil rank at least `14`. -/
public theorem curve198_hasRankGE_14 : HasRankGE curve198 14 := by
  unfold curve198
  certify_curve torsion 53 "data/curve198.txt" "data/curve198-labels.txt"

/-- Curve 198 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve198.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 198. -/
public theorem curve198_j : curve198.j = -388153332724011481538566057108013738948879904066499421232886819052761 / 1311295550412181298956751711791068502351802457869713490554687500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
