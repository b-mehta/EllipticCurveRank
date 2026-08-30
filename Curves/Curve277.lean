/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 277 has rank at least 6

The elliptic curve recorded as
[curve 277](https://elliptic-rank.icarm.cloud/curve/277) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -606045924`   and
  `a₆ = 5289852801024`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by Daksh Shami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 277 over `ℚ`. -/
@[expose] public def curve277 : WeierstrassCurve ℚ := ⟨0, 0, 0, -606045924, 5289852801024⟩

/-- ICARM leaderboard curve 277 has Mordell-Weil rank at least `6`. -/
public theorem curve277_hasRankGE_6 : HasRankGE curve277 6 := by
  unfold curve277
  certify_curve torsion 5 "data/curve277.txt" "data/curve277-labels.txt"

/-- Curve 277 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve277.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 277. -/
public theorem curve277_j : curve277.j = 4653682275070694592 / 407886758401321 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
