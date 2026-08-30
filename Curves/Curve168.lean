/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 168 has rank at least 16

The elliptic curve recorded as
[curve 168](https://elliptic-rank.icarm.cloud/curve/168) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -17499693052051780686008631`   and
  `a₆ = 24444545444646300140928746272873582761`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 168 over `ℚ`. -/
@[expose] public def curve168 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -17499693052051780686008631, 24444545444646300140928746272873582761⟩

/-- ICARM leaderboard curve 168 has Mordell-Weil rank at least `16`. -/
public theorem curve168_hasRankGE_16 : HasRankGE curve168 16 := by
  unfold curve168
  certify_curve torsion 41 "data/curve168.txt" "data/curve168-labels.txt"

/-- Curve 168 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve168.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 168. -/
public theorem curve168_j : curve168.j = 120633586947083765385366874558742798749564527915754238548350411616387713118913 / 17269791433986961699118075821819682707862187898136536760943740514838118400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
