/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 267 has rank at least 6

The elliptic curve recorded as
[curve 267](https://elliptic-rank.icarm.cloud/curve/267) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -2452`   and
  `a₆ = 2500`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 267 over `ℚ`. -/
@[expose] public def curve267 : WeierstrassCurve ℚ := ⟨0, 0, 0, -2452, 2500⟩

/-- ICARM leaderboard curve 267 has Mordell-Weil rank at least `6`. -/
public theorem curve267_hasRankGE_6 : HasRankGE curve267 6 := by
  unfold curve267
  certify_curve torsion 13 "data/curve267.txt" "data/curve267-labels.txt"

/-- Curve 267 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve267.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 267. -/
public theorem curve267_j : curve267.j = 6368617184256 / 3674995477 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
