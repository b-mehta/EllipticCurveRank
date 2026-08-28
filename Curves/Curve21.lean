/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 21 has rank at least 6

The elliptic curve recorded as
[curve 21](https://elliptic-rank.icarm.cloud/curve/21) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -852210116`   and
  `a₆ = 9511510378980`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve21.txt`; descent labels are in
`data/curve21-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 21 over `ℚ`. -/
@[expose] public def curve21 : WeierstrassCurve ℚ := ⟨0, -1, 0, -852210116, 9511510378980⟩

/-- ICARM leaderboard curve 21 has Mordell-Weil rank at least `6`. -/
public theorem curve21_hasRankGE_6 : HasRankGE curve21 6 := by
  unfold curve21
  certify_curve oneTorsion 62852 31 "data/curve21.txt" "data/curve21-labels.txt"

/-- Curve 21 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve21.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 21. -/
public theorem curve21_j : curve21.j = 354813083418250756987504 / 2753479396763095275 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
