/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 163 has rank at least 17

The elliptic curve recorded as
[curve 163](https://elliptic-rank.icarm.cloud/curve/163) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -22636258359102379085224610`   and
  `a₆ = 41564547766350787714309803970639244100`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve163.txt`; descent labels are in
`data/curve163-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 163 over `ℚ`. -/
@[expose] public def curve163 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -22636258359102379085224610, 41564547766350787714309803970639244100⟩

/-- ICARM leaderboard curve 163 has Mordell-Weil rank at least `17`. -/
public theorem curve163_hasRankGE_17 : HasRankGE curve163 17 := by
  unfold curve163
  certify_curve torsion 59 "data/curve163.txt" "data/curve163-labels.txt"

/-- Curve 163 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve163.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 163. -/
public theorem curve163_j : curve163.j = -8616086089688689275075367202757956991509522851358390026700151539034379055333 / 26891619238974740603451454564677901295160442410965033892041029324800000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
