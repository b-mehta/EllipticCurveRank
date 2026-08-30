/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 143 has rank at least 8

The elliptic curve recorded as
[curve 143](https://elliptic-rank.icarm.cloud/curve/143) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1336456`   and
  `a₆ = 594673996`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by cocoxhuang.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 143 over `ℚ`. -/
@[expose] public def curve143 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1336456, 594673996⟩

/-- ICARM leaderboard curve 143 has Mordell-Weil rank at least `8`. -/
public theorem curve143_hasRankGE_8 : HasRankGE curve143 8 := by
  unfold curve143
  certify_curve torsion 5 "data/curve143.txt" "data/curve143-labels.txt"

/-- Curve 143 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve143.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 143. -/
public theorem curve143_j : curve143.j = 263990251773289200957273 / 172501673868536644 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
