/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 40 has rank at least 20

The elliptic curve recorded as
[curve 40](https://elliptic-rank.icarm.cloud/curve/40) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -244537673336319601463803487168961769270757573821859853707`   and
  `a₆ = 9617101820531830345462229792588068177432706820289644342389578309898984381511`
  `     21499931`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve40.txt`; descent labels are in
`data/curve40-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 40 over `ℚ`. -/
@[expose] public def curve40 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -244537673336319601463803487168961769270757573821859853707,
    961710182053183034546222979258806817743270682028964434238957830989898438151121499931⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 40 has Mordell-Weil rank at least `20`. -/
public theorem curve40_hasRankGE_20 : HasRankGE curve40 20 := by
  unfold curve40
  certify_curve oneTorsion (-69288588686111702678625616725) 11 "data/curve40.txt" "data/curve40-labels.txt"

/-- Curve 40 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve40.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 40. -/
public theorem curve40_j : curve40.j = 986778376604714863187144673896668670633954068195910022898650009220478313927479626858189803118039781407817008771460743086812969840527237498224909421694448555984698699 / 327253952526479892358729374121654267775601616913273008692153366081310871797514250636466316047452603065873426523620705118520045561454150918662272037751521218240000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
