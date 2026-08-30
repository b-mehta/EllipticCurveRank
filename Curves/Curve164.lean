/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 164 has rank at least 17

The elliptic curve recorded as
[curve 164](https://elliptic-rank.icarm.cloud/curve/164) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -4936153897237243770097313`   and
  `a₆ = 4240417853491998596755638983929308017`

over `ℚ`. It has Mordell-Weil rank at least `17`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 164 over `ℚ`. -/
@[expose] public def curve164 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -4936153897237243770097313, 4240417853491998596755638983929308017⟩

/-- ICARM leaderboard curve 164 has Mordell-Weil rank at least `17`. -/
public theorem curve164_hasRankGE_17 : HasRankGE curve164 17 := by
  unfold curve164
  certify_curve torsion 13 "data/curve164.txt" "data/curve164-labels.txt"

/-- Curve 164 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve164.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 164. -/
public theorem curve164_j : curve164.j = -18245772615362737242635020688179842039641715002378927599458636447227404557001 / 96596297785511176202492530185517282392591841996495669883144724779827200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
