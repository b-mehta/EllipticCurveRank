/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 26 has rank at least 7

The elliptic curve recorded as
[curve 26](https://elliptic-rank.icarm.cloud/curve/26) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1485019900716`   and
  `a₆ = 658252007072023716`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 26 over `ℚ`. -/
@[expose] public def curve26 : WeierstrassCurve ℚ := ⟨0, -1, 0, -1485019900716, 658252007072023716⟩

/-- ICARM leaderboard curve 26 has Mordell-Weil rank at least `7`. -/
public theorem curve26_hasRankGE_7 : HasRankGE curve26 7 := by
  unfold curve26
  certify_curve oneTorsion 2256804 43 "data/curve26.txt" "data/curve26-labels.txt"

/-- Curve 26 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve26.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 26. -/
public theorem curve26_j : curve26.j = 27930286822977979655852256482253328 / 1728175896617050441636406899425 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
