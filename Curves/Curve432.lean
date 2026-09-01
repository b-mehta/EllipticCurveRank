/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 432 has rank at least 21

The elliptic curve recorded as
[curve 432](https://elliptic-rank.icarm.cloud/curve/432) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -134422478444183165897105480803299200`   and
  `a₆ = 19105637503606867472088832718752567503960757778399232`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 432 over `ℚ`. -/
@[expose] public def curve432 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -134422478444183165897105480803299200,
    19105637503606867472088832718752567503960757778399232⟩

/-- ICARM leaderboard curve 432 has Mordell-Weil rank at least `21`. -/
public theorem curve432_hasRankGE_21 : HasRankGE curve432 21 := by
  unfold curve432
  certify_curve torsion 19 "data/curve432.txt" "data/curve432-labels.txt"

/-- Curve 432 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve432.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 432. -/
public theorem curve432_j : curve432.j = -268620657473875726978320671213702439536744449659313009129105012494574846190695792806843968667121175353634764801 / 2239196697651177772152759233975931016330047275115124817633287595245219412904559503368757740795534131200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
