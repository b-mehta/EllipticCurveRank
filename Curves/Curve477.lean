/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 477 has rank at least 13

The elliptic curve recorded as
[curve 477](https://elliptic-rank.icarm.cloud/curve/477) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -3096136477`   and
  `a₆ = 19662705790596`

over `ℚ`. It has Mordell-Weil rank at least `13`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 477 over `ℚ`. -/
@[expose] public def curve477 : WeierstrassCurve ℚ := ⟨0, 0, 1, -3096136477, 19662705790596⟩

/-- ICARM leaderboard curve 477 has Mordell-Weil rank at least `13`. -/
public theorem curve477_hasRankGE_13 : HasRankGE curve477 13 := by
  unfold curve477
  certify_curve torsion 7 "data/curve477.txt" "data/curve477-labels.txt"

/-- Curve 477 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve477.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 477. -/
public theorem curve477_j : curve477.j = 3282343287301987789241736437723136 / 1732483513617389907070245271237 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
