/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 476 has rank at least 12

The elliptic curve recorded as
[curve 476](https://elliptic-rank.icarm.cloud/curve/476) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -332557057`   and
  `a₆ = 2359264710636`

over `ℚ`. It has Mordell-Weil rank at least `12`. Submitted to the leaderboard by NDElkies.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 476 over `ℚ`. -/
@[expose] public def curve476 : WeierstrassCurve ℚ := ⟨0, 0, 1, -332557057, 2359264710636⟩

/-- ICARM leaderboard curve 476 has Mordell-Weil rank at least `12`. -/
public theorem curve476_hasRankGE_12 : HasRankGE curve476 12 := by
  unfold curve476
  certify_curve torsion 7 "data/curve476.txt" "data/curve476-labels.txt"

/-- Curve 476 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve476.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 476. -/
public theorem curve476_j : curve476.j = -4067449940800548312396321632256 / 50719803766045246971171323 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
