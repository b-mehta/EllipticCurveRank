/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 235 has rank at least 15

The elliptic curve recorded as
[curve 235](https://elliptic-rank.icarm.cloud/curve/235) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -6073700298618828`   and
  `a₆ = 175770017627867226340148`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by RoyManami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 235 over `ℚ`. -/
@[expose] public def curve235 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -6073700298618828, 175770017627867226340148⟩

/-- ICARM leaderboard curve 235 has Mordell-Weil rank at least `15`. -/
public theorem curve235_hasRankGE_15 : HasRankGE curve235 15 := by
  unfold curve235
  certify_curve torsion 23 "data/curve235.txt" "data/curve235-labels.txt"

/-- Curve 235 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve235.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 235. -/
public theorem curve235_j : curve235.j = 132774994834696022512047371438578449224860681216 / 5320948175401041987715892274402717156524325 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
