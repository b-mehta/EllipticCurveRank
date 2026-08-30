/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 222 has rank at least 18

The elliptic curve recorded as
[curve 222](https://elliptic-rank.icarm.cloud/curve/222) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3331019292820252299857`   and
  `a₆ = 88471823270026370222046861281089`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by RoyManami.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 222 over `ℚ`. -/
@[expose] public def curve222 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -3331019292820252299857, 88471823270026370222046861281089⟩

/-- ICARM leaderboard curve 222 has Mordell-Weil rank at least `18`. -/
public theorem curve222_hasRankGE_18 : HasRankGE curve222 18 := by
  unfold curve222
  certify_curve torsion 13 "data/curve222.txt" "data/curve222-labels.txt"

/-- Curve 222 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve222.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 222. -/
public theorem curve222_j : curve222.j = -5606962197043039969108549947867214861860287407997389732530461976009 / 1393608587867013417022486645821340865286408196726383194163200000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
