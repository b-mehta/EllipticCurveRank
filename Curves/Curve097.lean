/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 97 has rank at least 17

The elliptic curve recorded as
[curve 97](https://elliptic-rank.icarm.cloud/curve/97) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -10363235273247623603445`   and
  `a₆ = 420203984207204686370404578747937`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 97 over `ℚ`. -/
@[expose] public def curve097 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -10363235273247623603445, 420203984207204686370404578747937⟩

/-- ICARM leaderboard curve 97 has Mordell-Weil rank at least `17`. -/
public theorem curve097_hasRankGE_17 : HasRankGE curve097 17 := by
  unfold curve097
  certify_curve torsion 19 "data/curve097.txt" "data/curve097-labels.txt"

/-- Curve 97 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve097.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 97. -/
public theorem curve097_j : curve097.j = -123086319549089222842077953482578248669768190747148118381851731517340881 / 5048330766436983365467936939800781032431719923365507757411328000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
