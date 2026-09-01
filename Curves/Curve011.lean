/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 11 has rank at least 28

The elliptic curve recorded as
[curve 11](https://elliptic-rank.icarm.cloud/curve/11) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -20067762415575526585033208209338542750930230312178956502`   and
  `a₆ = 3448161179503055646703298569039072037485594435931918036126600829629193944873`
  `     2243429`

over `ℚ`. It has Mordell-Weil rank at least `28`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 11, Elkies' rank-28 curve over `ℚ`. -/
@[expose] public def curve011 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -20067762415575526585033208209338542750930230312178956502,
    34481611795030556467032985690390720374855944359319180361266008296291939448732243429⟩

/-- ICARM leaderboard curve 11 has Mordell-Weil rank at least `28`. -/
public theorem curve011_hasRankGE_28 : HasRankGE curve011 28 := by
  unfold curve011
  certify_curve torsion 23 "data/curve011.txt" "data/curve011-labels.txt"

/-- Curve 11 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve011.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 11. -/
public theorem curve011_j : curve011.j = 1226007243212608888866916438050803469815245868601714575812830610588988145033634341671193988565188857512790532675609299974164298804872213167549130339154698870805175624729 / 4913271980221021357618307917397842063502840085350879228329798386467428719194915788099271692259622196339940966698514954093787531893856313165327458443714561536000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
