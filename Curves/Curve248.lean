/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 248 has rank at least 7

The elliptic curve recorded as
[curve 248](https://elliptic-rank.icarm.cloud/curve/248) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4719619360`   and
  `a₆ = 124799845948736`

over `ℚ`. It has Mordell-Weil rank at least `7`.

Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 248 over `ℚ`. -/
@[expose] public def curve248 : WeierstrassCurve ℚ := ⟨0, -1, 0, -4719619360, 124799845948736⟩

/-- ICARM leaderboard curve 248 has Mordell-Weil rank at least `7`. -/
public theorem curve248_hasRankGE_7 : HasRankGE curve248 7 := by
  unfold curve248
  certify_curve torsion 17 "data/curve248.txt" "data/curve248-labels.txt"

/-- Curve 248 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve248.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 248. -/
public theorem curve248_j : curve248.j = -2838472467928799790392654545441 / 203857978518193703 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
