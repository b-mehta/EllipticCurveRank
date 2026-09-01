/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 466 has rank at least 15

The elliptic curve recorded as
[curve 466](https://elliptic-rank.icarm.cloud/curve/466) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -1556038331383338`   and
  `a₆ = 23661751256860389864688`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Rayan Hatout.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 466 over `ℚ`. -/
@[expose] public def curve466 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -1556038331383338, 23661751256860389864688⟩

/-- ICARM leaderboard curve 466 has Mordell-Weil rank at least `15`. -/
public theorem curve466_hasRankGE_15 : HasRankGE curve466 15 := by
  unfold curve466
  certify_curve torsion 7 "data/curve466.txt" "data/curve466-labels.txt"

/-- Curve 466 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve466.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 466. -/
public theorem curve466_j : curve466.j = -416662663422148480203543323056389115525055407320601 / 743276271434381475440184156078589157200462500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
