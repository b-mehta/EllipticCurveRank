/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 174 has rank at least 16

The elliptic curve recorded as
[curve 174](https://elliptic-rank.icarm.cloud/curve/174) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2235680741254477841244774`   and
  `a₆ = 1283259936757609808257953240813254080`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve174.txt`; descent labels are in
`data/curve174-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 174 over `ℚ`. -/
@[expose] public def curve174 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -2235680741254477841244774, 1283259936757609808257953240813254080⟩

/-- ICARM leaderboard curve 174 has Mordell-Weil rank at least `16`. -/
public theorem curve174_hasRankGE_16 : HasRankGE curve174 16 := by
  unfold curve174
  certify_curve torsion 17 "data/curve174.txt" "data/curve174-labels.txt"

/-- Curve 174 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve174.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 174. -/
public theorem curve174_j : curve174.j = 1695217944601667365984388048441600021614384827152955744774624867409872302689 / 5173457030729210173229948875729928059837652709545887328254138834702500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
