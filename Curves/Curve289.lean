/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 289 has rank at least 1

The elliptic curve recorded as
[curve 289](https://elliptic-rank.icarm.cloud/curve/289) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = 1`   and
  `a₆ = 1000000000000000000000000000000000000000000000000000000000000000000000000000`
  `     0000000000000000000000000000000020000000000000000000000000000000000000000000`
  `     00000000000000000000000000000000000000000000000000000000000000001`

over `ℚ`. It has Mordell-Weil rank at least `1`. Submitted to the leaderboard by sorinmg.
-/

namespace ECCompute

open WeierstrassCurve

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 289 over `ℚ`. -/
@[expose] public def curve289 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 1,
    1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001⟩

/-- ICARM leaderboard curve 289 has Mordell-Weil rank at least `1`. -/
public theorem curve289_hasRankGE_1 : HasRankGE curve289 1 := by
  unfold curve289
  certify_curve torsion 5 "data/curve289.txt" "data/curve289-labels.txt"

/-- Curve 289 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve289.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 289. -/
public theorem curve289_j : curve289.j = 6912 / 27000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000162000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000031 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
