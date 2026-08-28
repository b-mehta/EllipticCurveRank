/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 239 has rank at least 15

The elliptic curve recorded as
[curve 239](https://elliptic-rank.icarm.cloud/curve/239) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -22359392011092389449`   and
  `a₆ = 40692284642676185167439218585`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve239.txt`; descent labels are in
`data/curve239-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 239 over `ℚ`. -/
@[expose] public def curve239 : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, -22359392011092389449, 40692284642676185167439218585⟩

/-- ICARM leaderboard curve 239 has Mordell-Weil rank at least `15`. -/
public theorem curve239_hasRankGE_15 : HasRankGE curve239 15 := by
  unfold curve239
  certify_curve torsion 31 "data/curve239.txt" "data/curve239-labels.txt"

/-- Curve 239 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve239.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 239. -/
public theorem curve239_j : curve239.j = 150908512763921905818505391229176344787144256016130179280096 / 10466080105740330466541740600326045104249922545964561 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
