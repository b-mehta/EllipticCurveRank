/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 285 has rank at least 21

The elliptic curve recorded as
[curve 285](https://elliptic-rank.icarm.cloud/curve/285) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -108391804584990603814796450120`   and
  `a₆ = 13755098120758219348428060610562384253731136`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 285 over `ℚ`. -/
@[expose] public def curve285 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -108391804584990603814796450120, 13755098120758219348428060610562384253731136⟩

/-- ICARM leaderboard curve 285 has Mordell-Weil rank at least `21`. -/
public theorem curve285_hasRankGE_21 : HasRankGE curve285 21 := by
  unfold curve285
  certify_curve torsion 11 "data/curve285.txt" "data/curve285-labels.txt"

/-- Curve 285 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve285.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 285. -/
public theorem curve285_j : curve285.j = -137534956958959875658649865753985413726619184818863411281142671036870152384737443964383524 / 227910338112679744969436886726814874185266384845663734114678771476940316478016394667 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
