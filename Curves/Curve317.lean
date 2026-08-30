/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 317 has rank at least 16

The elliptic curve recorded as
[curve 317](https://elliptic-rank.icarm.cloud/curve/317) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -4315862856022573416006`   and
  `a₆ = 107904629186874422701928761288036`

over `ℚ`. It has Mordell-Weil rank at least `16`.

Submitted to the leaderboard by Jack Cheng.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 317 over `ℚ`. -/
@[expose] public def curve317 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -4315862856022573416006, 107904629186874422701928761288036⟩

/-- ICARM leaderboard curve 317 has Mordell-Weil rank at least `16`. -/
public theorem curve317_hasRankGE_16 : HasRankGE curve317 16 := by
  unfold curve317
  certify_curve torsion 41 "data/curve317.txt" "data/curve317-labels.txt"

/-- Curve 317 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve317.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 317. -/
public theorem curve317_j : curve317.j = 8890508867207217481939709033561558715397718102886616500543423826121569 / 115017721248537024791512873609799594141037969992867713718881894400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
