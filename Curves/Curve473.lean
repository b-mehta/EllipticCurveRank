/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 473 has rank at least 9

The elliptic curve recorded as
[curve 473](https://elliptic-rank.icarm.cloud/curve/473) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2444705780`   and
  `a₆ = 53729427292247`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 473 over `ℚ`. -/
@[expose] public def curve473 : WeierstrassCurve ℚ := ⟨1, -1, 1, -2444705780, 53729427292247⟩

/-- ICARM leaderboard curve 473 has Mordell-Weil rank at least `9`. -/
public theorem curve473_hasRankGE_9 : HasRankGE curve473 9 := by
  unfold curve473
  certify_curve torsion 7 "data/curve473.txt" "data/curve473-labels.txt"

/-- Curve 473 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve473.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 473. -/
public theorem curve473_j : curve473.j = -3546467336381872752755708425 / 684746715107377798176768 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
