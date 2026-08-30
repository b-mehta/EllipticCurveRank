/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 385 has rank at least 29

The elliptic curve recorded as
[curve 385](https://elliptic-rank.icarm.cloud/curve/385) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -331827496674406562041164370816053963496434513510649284995530467`   and
  `a₆ = 2322853282053688692296179831887155386042997843373920023045057766047634710076`
  `     537198987220653859`

over `ℚ`. It has Mordell-Weil rank at least `29`. Submitted to the leaderboard by wgxli.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 385 over `ℚ`. -/
@[expose] public def curve385 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -331827496674406562041164370816053963496434513510649284995530467,
    2322853282053688692296179831887155386042997843373920023045057766047634710076537198987220653859⟩

/-- ICARM leaderboard curve 385 has Mordell-Weil rank at least `29`. -/
public theorem curve385_hasRankGE_29 : HasRankGE curve385 29 := by
  unfold curve385
  certify_curve torsion 31 "data/curve385.txt" "data/curve385-labels.txt"

/-- Curve 385 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve385.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 385. -/
public theorem curve385_j : curve385.j = 4040739232014149382404671605831145393430581927690769095539083208899705552098244821396534329236844622563484283376195833131104096922858468102168806500560539716467091799036539198313560467421667201 / 7471095450087195680727910445236600611605374236497648624054680031636234554634519268881655134072097590988924720904838797989784438432624613801399248973213649643196099694576440515449856000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
