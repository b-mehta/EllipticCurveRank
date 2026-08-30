/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 150 has rank at least 9

The elliptic curve recorded as
[curve 150](https://elliptic-rank.icarm.cloud/curve/150) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1743349`   and
  `a₆ = 886895689`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 150 over `ℚ`. -/
@[expose] public def curve150 : WeierstrassCurve ℚ := ⟨1, -1, 0, -1743349, 886895689⟩

/-- ICARM leaderboard curve 150 has Mordell-Weil rank at least `9`. -/
public theorem curve150_hasRankGE_9 : HasRankGE curve150 9 := by
  unfold curve150
  certify_curve torsion 23 "data/curve150.txt" "data/curve150-labels.txt"

/-- Curve 150 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve150.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 150. -/
public theorem curve150_j : curve150.j = -585971998525082176551081 / 366215869260338948 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
