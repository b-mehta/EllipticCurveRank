/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 389 has rank at least 24

The elliptic curve recorded as
[curve 389](https://elliptic-rank.icarm.cloud/curve/389) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1095282788134949493900735863144922358015`   and
  `a₆ = 15295153953560099274066571309175569823788527272931004403225`

over `ℚ`. It has Mordell-Weil rank at least `24`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve389.txt`; descent labels are in
`data/curve389-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 389 over `ℚ`. -/
@[expose] public def curve389 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1095282788134949493900735863144922358015,
    15295153953560099274066571309175569823788527272931004403225⟩

/-- ICARM leaderboard curve 389 has Mordell-Weil rank at least `24`. -/
public theorem curve389_hasRankGE_24 : HasRankGE curve389 24 := by
  unfold curve389
  certify_curve torsion 37 "data/curve389.txt" "data/curve389-labels.txt"

/-- Curve 389 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve389.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 389. -/
public theorem curve389_j : curve389.j = -145312341573618238586302764618873649193378825285336254419928980616037236937220045466761863728619821105661311821391634037361 / 16970039025550863782887325813264596680915050443093452753907786917780581431538468373817152988169621651380982872320000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
