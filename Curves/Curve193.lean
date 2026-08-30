/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 193 has rank at least 15

The elliptic curve recorded as
[curve 193](https://elliptic-rank.icarm.cloud/curve/193) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -87325226813408696187425`   and
  `a₆ = 8446101555990886693844233482455625`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 193 over `ℚ`. -/
@[expose] public def curve193 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -87325226813408696187425, 8446101555990886693844233482455625⟩

/-- ICARM leaderboard curve 193 has Mordell-Weil rank at least `15`. -/
public theorem curve193_hasRankGE_15 : HasRankGE curve193 15 := by
  unfold curve193
  certify_curve torsion 61 "data/curve193.txt" "data/curve193-labels.txt"

/-- Curve 193 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve193.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 193. -/
public theorem curve193_j : curve193.j = 73644934304869873813426088201777728890797943990126519718218634558433869201 / 11801171435734791180357853315012481673861744917479863238791703372800000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
