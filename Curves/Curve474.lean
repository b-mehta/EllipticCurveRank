/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 474 has rank at least 10

The elliptic curve recorded as
[curve 474](https://elliptic-rank.icarm.cloud/curve/474) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -323494567865`   and
  `a₆ = 68724510883515463`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 474 over `ℚ`. -/
@[expose] public def curve474 : WeierstrassCurve ℚ := ⟨0, 1, 0, -323494567865, 68724510883515463⟩

/-- ICARM leaderboard curve 474 has Mordell-Weil rank at least `10`. -/
public theorem curve474_hasRankGE_10 : HasRankGE curve474 10 := by
  unfold curve474
  certify_curve torsion 23 "data/curve474.txt" "data/curve474-labels.txt"

/-- Curve 474 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve474.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 474. -/
public theorem curve474_j : curve474.j = 62430095697280383019429466159296 / 2105125621096395749927665625 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
