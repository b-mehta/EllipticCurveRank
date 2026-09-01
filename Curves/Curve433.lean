/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 433 has rank at least 21

The elliptic curve recorded as
[curve 433](https://elliptic-rank.icarm.cloud/curve/433) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -1365250332763869332711550077906847`   and
  `a₆ = 20124145234049359349449557795949681874466874385250`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 433 over `ℚ`. -/
@[expose] public def curve433 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -1365250332763869332711550077906847, 20124145234049359349449557795949681874466874385250⟩

/-- ICARM leaderboard curve 433 has Mordell-Weil rank at least `21`. -/
public theorem curve433_hasRankGE_21 : HasRankGE curve433 21 := by
  unfold curve433
  certify_curve torsion 17 "data/curve433.txt" "data/curve433-labels.txt"

/-- Curve 433 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve433.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 433. -/
public theorem curve433_j : curve433.j = -628059706092055781149359452524263294174623521263957709900692353639620581147824075685720620427984 / 26983724778405469128465707819683263945687858399066963338314215617488279740646457280771093647 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
