/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 207 has rank at least 15

The elliptic curve recorded as
[curve 207](https://elliptic-rank.icarm.cloud/curve/207) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3341292704781910718198379200256`   and
  `a₆ = 2359087778502928782734938491871399298406363136`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 207 over `ℚ`. -/
@[expose] public def curve207 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3341292704781910718198379200256, 2359087778502928782734938491871399298406363136⟩

/-- ICARM leaderboard curve 207 has Mordell-Weil rank at least `15`. -/
public theorem curve207_hasRankGE_15 : HasRankGE curve207 15 := by
  unfold curve207
  certify_curve torsion 41 "data/curve207.txt" "data/curve207-labels.txt"

/-- Curve 207 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve207.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 207. -/
public theorem curve207_j : curve207.j = -839692966510787338234913549715848798864558983549878252014023265968348940687406914770378216913 / 3422870604766236676640461540968597637385614986383819869199981932113776785925252020121600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
