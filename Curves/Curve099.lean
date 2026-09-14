/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 99 has rank at least 10

The elliptic curve recorded as
[curve 99](https://elliptic-rank.icarm.cloud/curve/99) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -10194109`   and
  `a₆ = 12647638369`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 99 over `ℚ`. -/
@[expose] public def curve099 : WeierstrassCurve ℚ := ⟨1, -1, 0, -10194109, 12647638369⟩

/-- ICARM leaderboard curve 99 has Mordell-Weil rank at least `10`. -/
public theorem curve099_hasRankGE_10 : HasRankGE curve099 10 := by
  unfold curve099
  certify_curve torsion 7 "data/curve099.txt" "data/curve099-labels.txt"

/-- Curve 99 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve099.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 99. -/
public theorem curve099_j : curve099.j = -117157893629007724623028521 / 1276357388188605753068 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
