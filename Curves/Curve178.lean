/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 178 has rank at least 16

The elliptic curve recorded as
[curve 178](https://elliptic-rank.icarm.cloud/curve/178) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -231933522541838620953102503`   and
  `a₆ = 1359827717462320292062961439163457381087`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 178 over `ℚ`. -/
@[expose] public def curve178 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -231933522541838620953102503, 1359827717462320292062961439163457381087⟩

/-- ICARM leaderboard curve 178 has Mordell-Weil rank at least `16`. -/
public theorem curve178_hasRankGE_16 : HasRankGE curve178 16 := by
  unfold curve178
  certify_curve torsion 71 "data/curve178.txt" "data/curve178-labels.txt"

/-- Curve 178 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve178.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 178. -/
public theorem curve178_j : curve178.j = -66269446999022735422995542778655688628047999436367325736362859041338587257881 / 15984702572616129644036067033158033960203960410133606255083019758950400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
