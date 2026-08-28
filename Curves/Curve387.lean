/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 387 has rank at least 21

The elliptic curve recorded as
[curve 387](https://elliptic-rank.icarm.cloud/curve/387) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -100866462025735601489061531221367632`   and
  `a₆ = 12314457652529668478336154151601632727445624755257139`

over `ℚ`. It has Mordell-Weil rank at least `21`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve387.txt`; descent labels are in
`data/curve387-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 387 over `ℚ`. -/
@[expose] public def curve387 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -100866462025735601489061531221367632,
    12314457652529668478336154151601632727445624755257139⟩

/-- ICARM leaderboard curve 387 has Mordell-Weil rank at least `21`. -/
public theorem curve387_hasRankGE_21 : HasRankGE curve387 21 := by
  unfold curve387
  certify_curve torsion 29 "data/curve387.txt" "data/curve387-labels.txt"

/-- Curve 387 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve387.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 387. -/
public theorem curve387_j : curve387.j = 155681335099790708120116490480138872082430829065269233660262552215276375236422846189440961582975238912084409 / 229147574780948635963792405860493813920311074667067051887844097104668252706217793512705315063603200000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
