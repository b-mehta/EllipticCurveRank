/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import ECCompute.Tactic.CertifyCurve
import ECCompute.Soundness.JInvariant

/-!
# Curve 11 has rank at least 28

The elliptic curve recorded as
[curve 11](https://elliptic-rank.icarm.cloud/curve/11) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -20067762415575526585033208209338542750930230312178956502`   and
  `a₆ = 34481611795030556467032985690390720374855944359319180361266008296291939448732243429`

over `ℚ`. It has Mordell-Weil rank at least `28`, the 2006 rank record of N. D. Elkies. Points in
`data/curve11.txt`, descent labels in `data/curve11-labels.txt`; `certify_curve` does the rest.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 11, Elkies' rank-28 curve over `ℚ`. -/
def curve11 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -20067762415575526585033208209338542750930230312178956502,
    34481611795030556467032985690390720374855944359319180361266008296291939448732243429⟩

/-- ICARM leaderboard curve 11 has Mordell-Weil rank at least `28`. -/
theorem curve11_hasRankGE_28 : HasRankGE curve11 28 := by
  unfold curve11
  certify_curve torsion 23 "data/curve11.txt" "data/curve11-labels.txt"

/-- Curve 11 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
instance : curve11.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 11. -/
theorem curve11_j : curve11.j = 1226007243212608888866916438050803469815245868601714575812830610588988145033634341671193988565188857512790532675609299974164298804872213167549130339154698870805175624729 / 4913271980221021357618307917397842063502840085350879228329798386467428719194915788099271692259622196339940966698514954093787531893856313165327458443714561536000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
