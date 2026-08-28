/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 391 has rank at least 28

The elliptic curve recorded as
[curve 391](https://elliptic-rank.icarm.cloud/curve/391) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -253358083066972965014377893305253723955166094643129094555`   and
  `a₆ = 1581891748619190376056299653607794133364757942527274090543772455710877264718`
  `     525507025`

over `ℚ`. It has Mordell-Weil rank at least `28`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve391.txt`; descent labels are in
`data/curve391-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 391 over `ℚ`. -/
@[expose] public def curve391 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -253358083066972965014377893305253723955166094643129094555,
    1581891748619190376056299653607794133364757942527274090543772455710877264718525507025⟩

/-- ICARM leaderboard curve 391 has Mordell-Weil rank at least `28`. -/
public theorem curve391_hasRankGE_28 : HasRankGE curve391 28 := by
  unfold curve391
  certify_curve torsion 19 "data/curve391.txt" "data/curve391-labels.txt"

/-- Curve 391 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve391.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 391. -/
public theorem curve391_j : curve391.j = -818649401371543207243745332008487833430344030697331332345161580344276001816171118204404757480947046134810842636244096946781019907114774163569723298864661849043594971445293 / 18292265299058070625282765849390356407281102553060534335453130063736852706852899913915887716975081285924728295357867512931561770691034655440239562746058646697472000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
