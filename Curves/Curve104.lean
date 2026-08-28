/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 104 has rank at least 16

The elliptic curve recorded as
[curve 104](https://elliptic-rank.icarm.cloud/curve/104) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -28776016773697375`   and
  `a₆ = 1902573710284632656267650`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve104.txt`; descent labels are in
`data/curve104-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 104 over `ℚ`. -/
@[expose] public def curve104 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -28776016773697375, 1902573710284632656267650⟩

/-- ICARM leaderboard curve 104 has Mordell-Weil rank at least `16`. -/
public theorem curve104_hasRankGE_16 : HasRankGE curve104 16 := by
  unfold curve104
  certify_curve torsion 7 "data/curve104.txt" "data/curve104-labels.txt"

/-- Curve 104 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve104.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 104. -/
public theorem curve104_j : curve104.j = -16470082074050183813082412685012795071914577650000 / 242126655722010621584605257236918057412138767 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
