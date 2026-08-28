/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 220 has rank at least 15

The elliptic curve recorded as
[curve 220](https://elliptic-rank.icarm.cloud/curve/220) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -13842353204493057889413`   and
  `a₆ = 635570255797456549699738037418817`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve220.txt`; descent labels are in
`data/curve220-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 220 over `ℚ`. -/
@[expose] public def curve220 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -13842353204493057889413, 635570255797456549699738037418817⟩

/-- ICARM leaderboard curve 220 has Mordell-Weil rank at least `15`. -/
public theorem curve220_hasRankGE_15 : HasRankGE curve220 15 := by
  unfold curve220
  certify_curve torsion 17 "data/curve220.txt" "data/curve220-labels.txt"

/-- Curve 220 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve220.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 220. -/
public theorem curve220_j : curve220.j = -18772990738951319783949960641571463988007539294908977984965694510217 / 304397889719359412997262695274380998730610412423317862734299136 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
