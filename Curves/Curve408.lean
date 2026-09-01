/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 408 has rank at least 18

The elliptic curve recorded as
[curve 408](https://elliptic-rank.icarm.cloud/curve/408) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -276891740847977926726940094`   and
  `a₆ = 1884532832341693905066312410598171652600`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 408 over `ℚ`. -/
@[expose] public def curve408 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -276891740847977926726940094, 1884532832341693905066312410598171652600⟩

/-- ICARM leaderboard curve 408 has Mordell-Weil rank at least `18`. -/
public theorem curve408_hasRankGE_18 : HasRankGE curve408 18 := by
  unfold curve408
  certify_curve torsion 29 "data/curve408.txt" "data/curve408-labels.txt"

/-- Curve 408 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve408.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 408. -/
public theorem curve408_j : curve408.j = -3220521398220610995109639730584561115433226424954854509972880997447669120529827809 / 240843595984432982874189510496571441895296405674948975839831011377175174812500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
