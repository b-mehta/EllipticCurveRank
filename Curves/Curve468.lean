/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 468 has rank at least 10

The elliptic curve recorded as
[curve 468](https://elliptic-rank.icarm.cloud/curve/468) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -17449247001`   and
  `a₆ = 886897187503101`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by benvchurch.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 468 over `ℚ`. -/
@[expose] public def curve468 : WeierstrassCurve ℚ := ⟨0, -1, 0, -17449247001, 886897187503101⟩

/-- ICARM leaderboard curve 468 has Mordell-Weil rank at least `10`. -/
public theorem curve468_hasRankGE_10 : HasRankGE curve468 10 := by
  unfold curve468
  certify_curve torsion 13 "data/curve468.txt" "data/curve468-labels.txt"

/-- Curve 468 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve468.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 468. -/
public theorem curve468_j : curve468.j = 2295164499013252400738730617089024 / 872683003699293522919745925 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
