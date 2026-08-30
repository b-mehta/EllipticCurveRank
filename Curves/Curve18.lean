/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 18 has rank at least 6

The elliptic curve recorded as
[curve 18](https://elliptic-rank.icarm.cloud/curve/18) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2069247973`   and
  `a₆ = 36191779888342`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 18 over `ℚ`. -/
@[expose] public def curve18 : WeierstrassCurve ℚ := ⟨0, -1, 0, -2069247973, 36191779888342⟩

/-- ICARM leaderboard curve 18 has Mordell-Weil rank at least `6`. -/
public theorem curve18_hasRankGE_6 : HasRankGE curve18 6 := by
  unfold curve18
  certify_curve oneTorsion 107848 29 "data/curve18.txt" "data/curve18-labels.txt"

/-- Curve 18 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve18.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 18. -/
public theorem curve18_j : curve18.j = 1428358461822810424179949568 / 1769156629341263370351 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
