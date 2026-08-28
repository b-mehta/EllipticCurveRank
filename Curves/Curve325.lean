/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 325 has rank at least 13

The elliptic curve recorded as
[curve 325](https://elliptic-rank.icarm.cloud/curve/325) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -10144481942155625929509103657049467471830992522065306476640`   and
  `a₆ = 3802162866335172556011878234211341467779924436454813806909417922269783592668`
  `     52679415988`

over `ℚ`. It has Mordell-Weil rank at least `13`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve325.txt`; descent labels are in
`data/curve325-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 325 over `ℚ`. -/
@[expose] public def curve325 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -10144481942155625929509103657049467471830992522065306476640,
    380216286633517255601187823421134146777992443645481380690941792226978359266852679415988⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 325 has Mordell-Weil rank at least `13`. -/
public theorem curve325_hasRankGE_13 : HasRankGE curve325 13 := by
  unfold curve325
  certify_curve oneTorsion 266397362122413419597991786284 19 "data/curve325.txt" "data/curve325-labels.txt"

/-- Curve 325 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve325.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 325. -/
public theorem curve325_j : curve325.j = 28187293940821864762318032255471629866756174350157464621340138127633696452095767918121459720481585531203860698627322620723453049292805930901678018777510809231627481798187396961 / 1065062241652306812506484279874485101366505697571073066702727139643283352945685468753054505760896030394381025385087080696711058750653286163501893407992835258401943603515625 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
