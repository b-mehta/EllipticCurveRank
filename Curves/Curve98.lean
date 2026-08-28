/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 98 has rank at least 18

The elliptic curve recorded as
[curve 98](https://elliptic-rank.icarm.cloud/curve/98) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -81178834234583541704958093`   and
  `a₆ = 308750682382680533525277345167136070581`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve98.txt`; descent labels are in
`data/curve98-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 98 over `ℚ`. -/
@[expose] public def curve98 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -81178834234583541704958093, 308750682382680533525277345167136070581⟩

/-- ICARM leaderboard curve 98 has Mordell-Weil rank at least `18`. -/
public theorem curve98_hasRankGE_18 : HasRankGE curve98 18 := by
  unfold curve98
  certify_curve torsion 7 "data/curve98.txt" "data/curve98-labels.txt"

/-- Curve 98 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve98.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 98. -/
public theorem curve98_j : curve98.j = -59163266378591534431349037193513238571285544587053636208056901626994405222714882849 / 6943255656099873846088189823650058376374717862862923480133566806025633174732800 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
