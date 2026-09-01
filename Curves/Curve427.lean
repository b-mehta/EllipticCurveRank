/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 427 has rank at least 21

The elliptic curve recorded as
[curve 427](https://elliptic-rank.icarm.cloud/curve/427) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -26422761132426221314307634025955`   and
  `a₆ = 60338761815319965289688140627358385040885056547`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 427 over `ℚ`. -/
@[expose] public def curve427 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -26422761132426221314307634025955, 60338761815319965289688140627358385040885056547⟩

/-- ICARM leaderboard curve 427 has Mordell-Weil rank at least `21`. -/
public theorem curve427_hasRankGE_21 : HasRankGE curve427 21 := by
  unfold curve427
  certify_curve torsion 19 "data/curve427.txt" "data/curve427-labels.txt"

/-- Curve 427 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve427.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 427. -/
public theorem curve427_j : curve427.j = -179106255261224428137453754233946183381126843213903528691278725614016147178317223881080829153 / 34429975081741635563227247338801251163573973182894914701604345153215801454138786564276224 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
