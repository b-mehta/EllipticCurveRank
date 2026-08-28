/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 225 has rank at least 19

The elliptic curve recorded as
[curve 225](https://elliptic-rank.icarm.cloud/curve/225) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -74930448115659308831654455245038`   and
  `a₆ = 249563452537886885000166950293580142396024130692`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve225.txt`; descent labels are in
`data/curve225-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 225 over `ℚ`. -/
@[expose] public def curve225 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -74930448115659308831654455245038, 249563452537886885000166950293580142396024130692⟩

/-- ICARM leaderboard curve 225 has Mordell-Weil rank at least `19`. -/
public theorem curve225_hasRankGE_19 : HasRankGE curve225 19 := by
  unfold curve225
  certify_curve torsion 7 "data/curve225.txt" "data/curve225-labels.txt"

/-- Curve 225 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve225.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 225. -/
public theorem curve225_j : curve225.j = 2977684468848533631850428383391482875451523669945424324497297149513127276430036240156589786913817 / 1226593718604506851358593720287909600465672837010628863183698529253672991844810192530776064 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
