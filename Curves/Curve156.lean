/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 156 has rank at least 9

The elliptic curve recorded as
[curve 156](https://elliptic-rank.icarm.cloud/curve/156) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -759880`   and
  `a₆ = 142095100`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 156 over `ℚ`. -/
@[expose] public def curve156 : WeierstrassCurve ℚ := ⟨1, -1, 0, -759880, 142095100⟩

/-- ICARM leaderboard curve 156 has Mordell-Weil rank at least `9`. -/
public theorem curve156_hasRankGE_9 : HasRankGE curve156 9 := by
  unfold curve156
  certify_curve torsion 11 "data/curve156.txt" "data/curve156-labels.txt"

/-- Curve 156 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve156.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 156. -/
public theorem curve156_j : curve156.j = 48524277284657260860249 / 19381966510431193300 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
