/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 206 has rank at least 12

The elliptic curve recorded as
[curve 206](https://elliptic-rank.icarm.cloud/curve/206) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -374081627322112870915013649086`   and
  `a₆ = 84694590726964421851283320326657184990555716`

over `ℚ`. It has Mordell-Weil rank at least `12`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 206 over `ℚ`. -/
@[expose] public def curve206 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -374081627322112870915013649086, 84694590726964421851283320326657184990555716⟩

/-- ICARM leaderboard curve 206 has Mordell-Weil rank at least `12`. -/
public theorem curve206_hasRankGE_12 : HasRankGE curve206 12 := by
  unfold curve206
  certify_curve torsion 41 "data/curve206.txt" "data/curve206-labels.txt"

/-- Curve 206 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve206.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 206. -/
public theorem curve206_j : curve206.j = 5789257252176448678636349102426000827302087640431977695817089449036239484363937419021387134689 / 251453575815775763875321183856781238190717796098320943436148000167676873962388406215526400 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
