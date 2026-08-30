/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 4 has rank at least 15

The elliptic curve recorded as
[curve 4](https://elliptic-rank.icarm.cloud/curve/4) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -209811944511283096494753999485`   and
  `a₆ = 26653992551590286206010035905960909459942897`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 4 over `ℚ`. -/
@[expose] public def curve4 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -209811944511283096494753999485, 26653992551590286206010035905960909459942897⟩

/-- ICARM leaderboard curve 4 has Mordell-Weil rank at least `15`. -/
public theorem curve4_hasRankGE_15 : HasRankGE curve4 15 := by
  unfold curve4
  certify_curve torsion 29 "data/curve4.txt" "data/curve4-labels.txt"

/-- Curve 4 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve4.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 4. -/
public theorem curve4_j : curve4.j = 1021443474905391887241185106080413458447526690942639338949427731389929043874380451061511113041 / 284205064269551456641094292955182094002428922847801912953464227178522579040000000000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
