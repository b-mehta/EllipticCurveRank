/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 210 has rank at least 15

The elliptic curve recorded as
[curve 210](https://elliptic-rank.icarm.cloud/curve/210) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -14678039879640223236646547506`   and
  `a₆ = 596149475496280105667226784565254703843519`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 210 over `ℚ`. -/
@[expose] public def curve210 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -14678039879640223236646547506, 596149475496280105667226784565254703843519⟩

/-- ICARM leaderboard curve 210 has Mordell-Weil rank at least `15`. -/
public theorem curve210_hasRankGE_15 : HasRankGE curve210 15 := by
  unfold curve210
  certify_curve torsion 29 "data/curve210.txt" "data/curve210-labels.txt"

/-- Curve 210 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve210.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 210. -/
public theorem curve210_j : curve210.j = 349725985056112432278745059291246288657731140219920503008599854808842330415765359123777569 / 48857429671295622571237789586614535277793367429869518495768693667778413208750462668800 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
