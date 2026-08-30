/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 159 has rank at least 17

The elliptic curve recorded as
[curve 159](https://elliptic-rank.icarm.cloud/curve/159) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1321749187079172070`   and
  `a₆ = 247663242328119893241310696`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 159 over `ℚ`. -/
@[expose] public def curve159 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -1321749187079172070, 247663242328119893241310696⟩

/-- ICARM leaderboard curve 159 has Mordell-Weil rank at least `17`. -/
public theorem curve159_hasRankGE_17 : HasRankGE curve159 17 := by
  unfold curve159
  certify_curve torsion 7 "data/curve159.txt" "data/curve159-labels.txt"

/-- Curve 159 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve159.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 159. -/
public theorem curve159_j : curve159.j = 255370583047240462022392400085676178059986504554786914340409 / 121286283045713541182750044839266946611798283767937312700 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
