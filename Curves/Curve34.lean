/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 34 has rank at least 11

The elliptic curve recorded as
[curve 34](https://elliptic-rank.icarm.cloud/curve/34) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -115306530165769495485`   and
  `a₆ = 304950013864929098742150007444`

over `ℚ`. It has Mordell-Weil rank at least `11`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 34 over `ℚ`. -/
@[expose] public def curve34 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -115306530165769495485, 304950013864929098742150007444⟩

/-- ICARM leaderboard curve 34 has Mordell-Weil rank at least `11`. -/
public theorem curve34_hasRankGE_11 : HasRankGE curve34 11 := by
  unfold curve34
  certify_curve oneTorsion 11376943312 5 "data/curve34.txt" "data/curve34-labels.txt"

/-- Curve 34 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve34.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 34. -/
public theorem curve34_j : curve34.j = 10596573132490679629146791681939777040929724885906880577921744896 / 3621424321888632432629450530248713201918732250053936693011157 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
