/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 16 has rank at least 6

The elliptic curve recorded as
[curve 16](https://elliptic-rank.icarm.cloud/curve/16) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -23308665`   and
  `a₆ = 43082703225`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 16 over `ℚ`. -/
@[expose] public def curve16 : WeierstrassCurve ℚ := ⟨0, -1, 0, -23308665, 43082703225⟩

/-- ICARM leaderboard curve 16 has Mordell-Weil rank at least `6`. -/
public theorem curve16_hasRankGE_6 : HasRankGE curve16 6 := by
  unfold curve16
  certify_curve oneTorsion 11820 11 "data/curve16.txt" "data/curve16-labels.txt"

/-- Curve 16 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve16.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 16. -/
public theorem curve16_j : curve16.j = 341913290879033644447936 / 2174505011398265625 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
