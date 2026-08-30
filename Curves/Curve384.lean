/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 384 has rank at least 18

The elliptic curve recorded as
[curve 384](https://elliptic-rank.icarm.cloud/curve/384) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -65838560278746184445004976255`   and
  `a₆ = 7804621801493663292406561910967222627057125`

over `ℚ`. It has Mordell-Weil rank at least `18`.

Submitted to the leaderboard by y011d4.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 384 over `ℚ`. -/
@[expose] public def curve384 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -65838560278746184445004976255, 7804621801493663292406561910967222627057125⟩

/-- ICARM leaderboard curve 384 has Mordell-Weil rank at least `18`. -/
public theorem curve384_hasRankGE_18 : HasRankGE curve384 18 := by
  unfold curve384
  certify_curve torsion 17 "data/curve384.txt" "data/curve384-labels.txt"

/-- Curve 384 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve384.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 384. -/
public theorem curve384_j : curve384.j = -31562012559558477201324330637876379684744483542417065866760022981090788481102218110496977521 / 8048982908040164938257367514212363435923458637934622402798571165236429219655936000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
