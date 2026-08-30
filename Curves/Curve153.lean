/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 153 has rank at least 9

The elliptic curve recorded as
[curve 153](https://elliptic-rank.icarm.cloud/curve/153) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1240549`   and
  `a₆ = 521297989`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 153 over `ℚ`. -/
@[expose] public def curve153 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1240549, 521297989⟩

/-- ICARM leaderboard curve 153 has Mordell-Weil rank at least `9`. -/
public theorem curve153_hasRankGE_9 : HasRankGE curve153 9 := by
  unfold curve153
  certify_curve torsion 7 "data/curve153.txt" "data/curve153-labels.txt"

/-- Curve 153 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve153.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 153. -/
public theorem curve153_j : curve153.j = 211137647347999957843881 / 4929094923734171152 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
