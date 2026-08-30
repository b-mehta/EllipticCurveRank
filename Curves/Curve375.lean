/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 375 has rank at least 18

The elliptic curve recorded as
[curve 375](https://elliptic-rank.icarm.cloud/curve/375) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -5294538512342122389440470772`   and
  `a₆ = 147333838524398950267979074374742550207319`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Christopher R.
Hill.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 375 over `ℚ`. -/
@[expose] public def curve375 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -5294538512342122389440470772, 147333838524398950267979074374742550207319⟩

/-- ICARM leaderboard curve 375 has Mordell-Weil rank at least `18`. -/
public theorem curve375_hasRankGE_18 : HasRankGE curve375 18 := by
  unfold curve375
  certify_curve torsion 29 "data/curve375.txt" "data/curve375-labels.txt"

/-- Curve 375 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve375.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 375. -/
public theorem curve375_j : curve375.j = 788328285858748360075259301653156966343346545487398630469431668884169998645304809 / 5819455440532883078558130408532245184972505919864122540273680906080000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
