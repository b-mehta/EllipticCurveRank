/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 250 has rank at least 7

The elliptic curve recorded as
[curve 250](https://elliptic-rank.icarm.cloud/curve/250) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1926296120`   and
  `a₆ = 32541777273856`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve250.txt`; descent labels are in
`data/curve250-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 250 over `ℚ`. -/
@[expose] public def curve250 : WeierstrassCurve ℚ := ⟨0, -1, 0, -1926296120, 32541777273856⟩

/-- ICARM leaderboard curve 250 has Mordell-Weil rank at least `7`. -/
public theorem curve250_hasRankGE_7 : HasRankGE curve250 7 := by
  unfold curve250
  certify_curve torsion 7 "data/curve250.txt" "data/curve250-labels.txt"

/-- Curve 250 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve250.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 250. -/
public theorem curve250_j : curve250.j = -771956636741108239282352759524 / 21456111114079902767 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
