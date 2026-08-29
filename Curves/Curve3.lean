/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 3 has rank at least 14

The elliptic curve recorded as
[curve 3](https://elliptic-rank.icarm.cloud/curve/3) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -2248232106757`   and
  `a₆ = 1329472091379662406`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve3.txt`; descent labels are in
`data/curve3-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 3 over `ℚ`. -/
@[expose] public def curve3 : WeierstrassCurve ℚ := ⟨0, 0, 1, -2248232106757, 1329472091379662406⟩

/-- ICARM leaderboard curve 3 has Mordell-Weil rank at least `14`. -/
public theorem curve3_hasRankGE_14 : HasRankGE curve3 14 := by
  unfold curve3
  certify_curve torsion 7 "data/curve3.txt" "data/curve3-labels.txt"

/-- Curve 3 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve3.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 3. -/
public theorem curve3_j : curve3.j = -1256744950745018488654006246189184051245056 / 36275332432131715984679943280544970923 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
