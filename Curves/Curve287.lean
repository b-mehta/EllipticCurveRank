/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 287 has rank at least 1

The elliptic curve recorded as
[curve 287](https://elliptic-rank.icarm.cloud/curve/287) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -282081209084769804505293`   and
  `a₆ = -57664608560601805089739376623616957`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by sorinmg.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 287 over `ℚ`. -/
@[expose] public def curve287 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -282081209084769804505293, -57664608560601805089739376623616957⟩

/-- ICARM leaderboard curve 287 has Mordell-Weil rank at least `1`. -/
public theorem curve287_hasRankGE_1 : HasRankGE curve287 1 := by
  unfold curve287
  certify_curve oneTorsion 2453106695692 7 "data/curve287.txt" "data/curve287-labels.txt"

/-- Curve 287 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve287.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 287. -/
public theorem curve287_j : curve287.j = 3113888862328349554244611408146188288 / 52890226703106864903841 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
