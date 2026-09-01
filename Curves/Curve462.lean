/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 462 has rank at least 20

The elliptic curve recorded as
[curve 462](https://elliptic-rank.icarm.cloud/curve/462) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -5831269123044942826740026401456095`   and
  `a₆ = 133924295711655587194437025768409363893193455880025`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 462 over `ℚ`. -/
@[expose] public def curve462 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -5831269123044942826740026401456095,
    133924295711655587194437025768409363893193455880025⟩

/-- ICARM leaderboard curve 462 has Mordell-Weil rank at least `20`. -/
public theorem curve462_hasRankGE_20 : HasRankGE curve462 20 := by
  unfold curve462
  certify_curve torsion 23 "data/curve462.txt" "data/curve462-labels.txt"

/-- Curve 462 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve462.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 462. -/
public theorem curve462_j : curve462.j = 186390909714957039581805375213281460308748775338369604456468384119502532637778978619821932897353158369 / 42006243702637877251911084368160835312858683627622726477325711032485323409878874148199078400000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
