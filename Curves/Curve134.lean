/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 134 has rank at least 9

The elliptic curve recorded as
[curve 134](https://elliptic-rank.icarm.cloud/curve/134) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1493028`   and
  `a₆ = 701820182`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 134 over `ℚ`. -/
@[expose] public def curve134 : WeierstrassCurve ℚ := ⟨1, 0, 1, -1493028, 701820182⟩

/-- ICARM leaderboard curve 134 has Mordell-Weil rank at least `9`. -/
public theorem curve134_hasRankGE_9 : HasRankGE curve134 9 := by
  unfold curve134
  certify_curve torsion 7 "data/curve134.txt" "data/curve134-labels.txt"

/-- Curve 134 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve134.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 134. -/
public theorem curve134_j : curve134.j = 368067228871731007871161 / 144140151820290812 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
