/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 189 has rank at least 17

The elliptic curve recorded as
[curve 189](https://elliptic-rank.icarm.cloud/curve/189) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -165634403178213270286613816`   and
  `a₆ = 799855393883091839227487570305634706496`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve189.txt`; descent labels are in
`data/curve189-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 189 over `ℚ`. -/
@[expose] public def curve189 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -165634403178213270286613816, 799855393883091839227487570305634706496⟩

/-- ICARM leaderboard curve 189 has Mordell-Weil rank at least `17`. -/
public theorem curve189_hasRankGE_17 : HasRankGE curve189 17 := by
  unfold curve189
  certify_curve torsion 37 "data/curve189.txt" "data/curve189-labels.txt"

/-- Curve 189 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve189.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 189. -/
public theorem curve189_j : curve189.j = 502545459688220644107917573959681665398615093059375719453662391080093209866790055809 / 14444861515529646982364107927886725142451411941867709623555198879792460966963200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
