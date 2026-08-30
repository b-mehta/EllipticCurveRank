/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 17 has rank at least 6

The elliptic curve recorded as
[curve 17](https://elliptic-rank.icarm.cloud/curve/17) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -832328021`   and
  `a₆ = 9183124281870`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 17 over `ℚ`. -/
@[expose] public def curve17 : WeierstrassCurve ℚ := ⟨0, -1, 0, -832328021, 9183124281870⟩

/-- ICARM leaderboard curve 17 has Mordell-Weil rank at least `6`. -/
public theorem curve17_hasRankGE_6 : HasRankGE curve17 6 := by
  unfold curve17
  certify_curve oneTorsion 70952 31 "data/curve17.txt" "data/curve17-labels.txt"

/-- Curve 17 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve17.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 17. -/
public theorem curve17_j : curve17.j = 3985540964247579921431463460864 / 29681063325213354456927525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
