/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 241 has rank at least 18

The elliptic curve recorded as
[curve 241](https://elliptic-rank.icarm.cloud/curve/241) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -3002323607176717877406`   and
  `a₆ = 63157734310826839052785319777928`

over `ℚ`. It has Mordell-Weil rank at least `18`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 241 over `ℚ`. -/
@[expose] public def curve241 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -3002323607176717877406, 63157734310826839052785319777928⟩

/-- ICARM leaderboard curve 241 has Mordell-Weil rank at least `18`. -/
public theorem curve241_hasRankGE_18 : HasRankGE curve241 18 := by
  unfold curve241
  certify_curve torsion 19 "data/curve241.txt" "data/curve241-labels.txt"

/-- Curve 241 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve241.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 241. -/
public theorem curve241_j : curve241.j = 2992927629164878617015030101337837028781876776575774882001656942675169 / 8813761630935831317440473226115886471150831299234006905672050675 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
