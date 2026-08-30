/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 142 has rank at least 8

The elliptic curve recorded as
[curve 142](https://elliptic-rank.icarm.cloud/curve/142) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -2220127`   and
  `a₆ = 1296242146`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by cocoxhuang.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 142 over `ℚ`. -/
@[expose] public def curve142 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2220127, 1296242146⟩

/-- ICARM leaderboard curve 142 has Mordell-Weil rank at least `8`. -/
public theorem curve142_hasRankGE_8 : HasRankGE curve142 8 := by
  unfold curve142
  certify_curve torsion 7 "data/curve142.txt" "data/curve142-labels.txt"

/-- Curve 142 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve142.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 142. -/
public theorem curve142_j : curve142.j = -4727343957618753381456 / 99679788594734375 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
