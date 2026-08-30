/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 299 has rank at least 1

The elliptic curve recorded as
[curve 299](https://elliptic-rank.icarm.cloud/curve/299) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 0`   and
  `a₆ = 1000000000590000000087024`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 299 over `ℚ`. -/
@[expose] public def curve299 : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1000000000590000000087024⟩

/-- ICARM leaderboard curve 299 has Mordell-Weil rank at least `1`. -/
public theorem curve299_hasRankGE_1 : HasRankGE curve299 1 := by
  unfold curve299
  certify_curve torsion 7 "data/curve299.txt" "data/curve299-labels.txt"

/-- Curve 299 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve299.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 299. -/
public theorem curve299_j : curve299.j = 0 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
