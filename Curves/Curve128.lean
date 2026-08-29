/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 128 has rank at least 7

The elliptic curve recorded as
[curve 128](https://elliptic-rank.icarm.cloud/curve/128) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -22221159`   and
  `a₆ = 40791791609`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve128.txt`; descent labels are in
`data/curve128-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 128 over `ℚ`. -/
@[expose] public def curve128 : WeierstrassCurve ℚ := ⟨1, -1, 0, -22221159, 40791791609⟩

/-- ICARM leaderboard curve 128 has Mordell-Weil rank at least `7`. -/
public theorem curve128_hasRankGE_7 : HasRankGE curve128 7 := by
  unfold curve128
  certify_curve torsion 7 "data/curve128.txt" "data/curve128-labels.txt"

/-- Curve 128 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve128.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 128. -/
public theorem curve128_j : curve128.j = -1664547970304784084296049 / 22507819754899520492 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
