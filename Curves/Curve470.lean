/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 470 has rank at least 10

The elliptic curve recorded as
[curve 470](https://elliptic-rank.icarm.cloud/curve/470) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -315277608363`   and
  `a₆ = 72862525021888281`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 470 over `ℚ`. -/
@[expose] public def curve470 : WeierstrassCurve ℚ := ⟨1, 1, 1, -315277608363, 72862525021888281⟩

/-- ICARM leaderboard curve 470 has Mordell-Weil rank at least `10`. -/
public theorem curve470_hasRankGE_10 : HasRankGE curve470 10 := by
  unfold curve470
  certify_curve torsion 17 "data/curve470.txt" "data/curve470-labels.txt"

/-- Curve 470 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve470.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 470. -/
public theorem curve470_j : curve470.j = -221810994132393331214046791773161193 / 18419467380283262475280576364544 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
