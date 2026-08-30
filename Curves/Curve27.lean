/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 27 has rank at least 7

The elliptic curve recorded as
[curve 27](https://elliptic-rank.icarm.cloud/curve/27) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3225667994796`   and
  `a₆ = 2205916672708538820`

over `ℚ`. It has Mordell-Weil rank at least `7`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 27 over `ℚ`. -/
@[expose] public def curve27 : WeierstrassCurve ℚ := ⟨0, -1, 0, -3225667994796, 2205916672708538820⟩

/-- ICARM leaderboard curve 27 has Mordell-Weil rank at least `7`. -/
public theorem curve27_hasRankGE_7 : HasRankGE curve27 7 := by
  unfold curve27
  certify_curve oneTorsion 3791652 47 "data/curve27.txt" "data/curve27-labels.txt"

/-- Curve 27 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve27.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 27. -/
public theorem curve27_j : curve27.j = 14499156657276224279322827273382391293904 / 179233293942874401038192528800323525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
