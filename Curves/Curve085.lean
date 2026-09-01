/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 85 has rank at least 17

The elliptic curve recorded as
[curve 85](https://elliptic-rank.icarm.cloud/curve/85) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -12300937281145149633363`   and
  `a₆ = 178186913040613669561994205239138`

over `ℚ`. It has Mordell-Weil rank at least `17`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 85 over `ℚ`. -/
@[expose] public def curve085 : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -12300937281145149633363, 178186913040613669561994205239138⟩

/-- ICARM leaderboard curve 85 has Mordell-Weil rank at least `17`. -/
public theorem curve085_hasRankGE_17 : HasRankGE curve085 17 := by
  unfold curve085
  certify_curve torsion 13 "data/curve085.txt" "data/curve085-labels.txt"

/-- Curve 85 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve085.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 85. -/
public theorem curve085_j : curve085.j = 275747027586766345812718774160256259569428506955695961863606098244 / 141201650236008754630417641721102170710996636040903701629536525 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
