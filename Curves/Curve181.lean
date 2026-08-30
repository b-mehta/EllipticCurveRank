/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 181 has rank at least 16

The elliptic curve recorded as
[curve 181](https://elliptic-rank.icarm.cloud/curve/181) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3994635920327174224332`   and
  `a₆ = 100608973921885468649536289354896`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 181 over `ℚ`. -/
@[expose] public def curve181 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3994635920327174224332, 100608973921885468649536289354896⟩

/-- ICARM leaderboard curve 181 has Mordell-Weil rank at least `16`. -/
public theorem curve181_hasRankGE_16 : HasRankGE curve181 16 := by
  unfold curve181
  certify_curve torsion 5 "data/curve181.txt" "data/curve181-labels.txt"

/-- Curve 181 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve181.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 181. -/
public theorem curve181_j : curve181.j = -7049451401799301771124089763998247944772873668265237035427154742325953 / 293231918449934958705327201280235162673170146698422177169348591616 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
