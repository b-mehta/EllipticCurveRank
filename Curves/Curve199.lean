/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 199 has rank at least 13

The elliptic curve recorded as
[curve 199](https://elliptic-rank.icarm.cloud/curve/199) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -20820207864197471248300179976626`   and
  `a₆ = 36732936589138673862895758597955508398047757956`

over `ℚ`. It has Mordell-Weil rank at least `13`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 199 over `ℚ`. -/
@[expose] public def curve199 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -20820207864197471248300179976626, 36732936589138673862895758597955508398047757956⟩

/-- ICARM leaderboard curve 199 has Mordell-Weil rank at least `13`. -/
public theorem curve199_hasRankGE_13 : HasRankGE curve199 13 := by
  unfold curve199
  certify_curve torsion 31 "data/curve199.txt" "data/curve199-labels.txt"

/-- Curve 199 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve199.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 199. -/
public theorem curve199_j : curve199.j = -998111122979483578061542693901648305995589525204645301641605323632809980564888443203235113786351649 / 5290724783356970045570091261064369041862691109828850503901233859803837652758778996437693235200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
