/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 230 has rank at least 17

The elliptic curve recorded as
[curve 230](https://elliptic-rank.icarm.cloud/curve/230) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -681626561473549068876`   and
  `a₆ = 6906843129225400827472871428396`

over `ℚ`. It has Mordell-Weil rank at least `17`.

Submitted to the leaderboard by Alexey Pozdnyakov.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 230 over `ℚ`. -/
@[expose] public def curve230 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -681626561473549068876, 6906843129225400827472871428396⟩

/-- ICARM leaderboard curve 230 has Mordell-Weil rank at least `17`. -/
public theorem curve230_hasRankGE_17 : HasRankGE curve230 17 := by
  unfold curve230
  certify_curve torsion 5 "data/curve230.txt" "data/curve230-labels.txt"

/-- Curve 230 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve230.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 230. -/
public theorem curve230_j : curve230.j = -48043617486627747346710908264239068802355000878737680608862721217 / 466303293386236189277479511850825311216685993099793223213484 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
