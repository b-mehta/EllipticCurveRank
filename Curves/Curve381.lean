/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 381 has rank at least 19

The elliptic curve recorded as
[curve 381](https://elliptic-rank.icarm.cloud/curve/381) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -109823651656505846940102737179`   and
  `a₆ = 13881034132195426802661701381391692661966985`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by y011d4.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 381 over `ℚ`. -/
@[expose] public def curve381 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -109823651656505846940102737179, 13881034132195426802661701381391692661966985⟩

/-- ICARM leaderboard curve 381 has Mordell-Weil rank at least `19`. -/
public theorem curve381_hasRankGE_19 : HasRankGE curve381 19 := by
  unfold curve381
  certify_curve torsion 47 "data/curve381.txt" "data/curve381-labels.txt"

/-- Curve 381 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve381.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 381. -/
public theorem curve381_j : curve381.j = 146491137762203728471853115124942944542953167854279935239670236835120724142312170413881633801 / 1535861076553756069541566097526976300456021823719770432861083465864224153832843577587500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
