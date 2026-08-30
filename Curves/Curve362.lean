/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 362 has rank at least 7

The elliptic curve recorded as
[curve 362](https://elliptic-rank.icarm.cloud/curve/362) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4886412`   and
  `a₆ = 4017333135`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 362 over `ℚ`. -/
@[expose] public def curve362 : WeierstrassCurve ℚ := ⟨1, -1, 1, -4886412, 4017333135⟩

/-- ICARM leaderboard curve 362 has Mordell-Weil rank at least `7`. -/
public theorem curve362_hasRankGE_7 : HasRankGE curve362 7 := by
  unfold curve362
  certify_curve torsion 19 "data/curve362.txt" "data/curve362-labels.txt"

/-- Curve 362 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve362.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 362. -/
public theorem curve362_j : curve362.j = 5374050144882456837681 / 207944574054449152 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
