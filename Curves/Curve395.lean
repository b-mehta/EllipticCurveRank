/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 395 has rank at least 28

The elliptic curve recorded as
[curve 395](https://elliptic-rank.icarm.cloud/curve/395) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1571436138788579721131230519678999674817868532078561707`   and
  `a₆ = 7457286452446900148911255668860540098864637891562817598018298479870456679402`
  `     20539`

over `ℚ`. It has Mordell-Weil rank at least `28`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve395.txt`; descent labels are in
`data/curve395-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 395 over `ℚ`. -/
@[expose] public def curve395 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -1571436138788579721131230519678999674817868532078561707,
    745728645244690014891125566886054009886463789156281759801829847987045667940220539⟩

/-- ICARM leaderboard curve 395 has Mordell-Weil rank at least `28`. -/
public theorem curve395_hasRankGE_28 : HasRankGE curve395 28 := by
  unfold curve395
  certify_curve torsion 47 "data/curve395.txt" "data/curve395-labels.txt"

/-- Curve 395 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve395.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 395. -/
public theorem curve395_j : curve395.j = 588689640533196722140692811939993697563679519041524530323736780102595850136313291983771549185058819213440126745437730952661132597249618737006577900160681767036341609 / 11129490219092854759152200486563237133920974273919284727522190341094378651390549220807052395505015400645194790823492220787825933461852149026643201815879680000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
