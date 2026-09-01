/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 86 has rank at least 15

The elliptic curve recorded as
[curve 86](https://elliptic-rank.icarm.cloud/curve/86) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -52841283229846206`   and
  `a₆ = -192819150610486916434364`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 86 over `ℚ`. -/
@[expose] public def curve086 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -52841283229846206, -192819150610486916434364⟩

/-- ICARM leaderboard curve 86 has Mordell-Weil rank at least `15`. -/
public theorem curve086_hasRankGE_15 : HasRankGE curve086 15 := by
  unfold curve086
  certify_curve torsion 17 "data/curve086.txt" "data/curve086-labels.txt"

/-- Curve 86 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve086.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 86. -/
public theorem curve086_j : curve086.j = 16317130215713413702729822682562798536092480225965766369 / 9426722265250752028761189313525609860226811622809600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
