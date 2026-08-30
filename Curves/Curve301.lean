/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 301 has rank at least 10

The elliptic curve recorded as
[curve 301](https://elliptic-rank.icarm.cloud/curve/301) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -11454891505`   and
  `a₆ = 535951116234579`

over `ℚ`. It has Mordell-Weil rank at least `10`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 301 over `ℚ`. -/
@[expose] public def curve301 : WeierstrassCurve ℚ := ⟨0, 1, 0, -11454891505, 535951116234579⟩

/-- ICARM leaderboard curve 301 has Mordell-Weil rank at least `10`. -/
public theorem curve301_hasRankGE_10 : HasRankGE curve301 10 := by
  unfold curve301
  certify_curve torsion 7 "data/curve301.txt" "data/curve301-labels.txt"

/-- Curve 301 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve301.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 301. -/
public theorem curve301_j : curve301.j = -649316871102534000494420912321536 / 108968401810731977801235808963 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
