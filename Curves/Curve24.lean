/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 24 has rank at least 6

The elliptic curve recorded as
[curve 24](https://elliptic-rank.icarm.cloud/curve/24) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2388994756`   and
  `a₆ = 44907381038500`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 24 over `ℚ`. -/
@[expose] public def curve24 : WeierstrassCurve ℚ := ⟨0, -1, 0, -2388994756, 44907381038500⟩

/-- ICARM leaderboard curve 24 has Mordell-Weil rank at least `6`. -/
public theorem curve24_hasRankGE_6 : HasRankGE curve24 6 := by
  unfold curve24
  certify_curve oneTorsion 110212 29 "data/curve24.txt" "data/curve24-labels.txt"

/-- Curve 24 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve24.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 24. -/
public theorem curve24_j : curve24.j = 5890190437726738405327986193744 / 5660243641291976370659025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
