/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 249 has rank at least 7

The elliptic curve recorded as
[curve 249](https://elliptic-rank.icarm.cloud/curve/249) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -7547876161`   and
  `a₆ = 252395109012864`

over `ℚ`. It has Mordell-Weil rank at least `7`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve249.txt`; descent labels are in
`data/curve249-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 249 over `ℚ`. -/
@[expose] public def curve249 : WeierstrassCurve ℚ := ⟨0, 1, 0, -7547876161, 252395109012864⟩

/-- ICARM leaderboard curve 249 has Mordell-Weil rank at least `7`. -/
public theorem curve249_hasRankGE_7 : HasRankGE curve249 7 := by
  unfold curve249
  certify_curve torsion 13 "data/curve249.txt" "data/curve249-labels.txt"

/-- Curve 249 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve249.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 249. -/
public theorem curve249_j : curve249.j = -2972199984653541671380695983079424 / 10197911483879944567675 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
