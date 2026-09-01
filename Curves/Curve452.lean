/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 452 has rank at least 20

The elliptic curve recorded as
[curve 452](https://elliptic-rank.icarm.cloud/curve/452) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -55000206503542170766038007004896613`   and
  `a₆ = 5296677150314724213014972255851724752418661641474817`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 452 over `ℚ`. -/
@[expose] public def curve452 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -55000206503542170766038007004896613,
    5296677150314724213014972255851724752418661641474817⟩

/-- ICARM leaderboard curve 452 has Mordell-Weil rank at least `20`. -/
public theorem curve452_hasRankGE_20 : HasRankGE curve452 20 := by
  unfold curve452
  certify_curve torsion 17 "data/curve452.txt" "data/curve452-labels.txt"

/-- Curve 452 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve452.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 452. -/
public theorem curve452_j : curve452.j = -29439922003774002762950798545352631453892972662517887967757031178396221572452969858655601707184067214761825 / 2354478142189036078613685933695188098679512671377931734105912607044587347810567956827974729499861123072 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
