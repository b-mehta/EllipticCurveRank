/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 162 has rank at least 9

The elliptic curve recorded as
[curve 162](https://elliptic-rank.icarm.cloud/curve/162) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -1029869656`   and
  `a₆ = 15913087721444`

over `ℚ`. It has Mordell-Weil rank at least `9`.

Submitted to the leaderboard by Seewoo Lee.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 162 over `ℚ`. -/
@[expose] public def curve162 : WeierstrassCurve ℚ := ⟨0, 1, 0, -1029869656, 15913087721444⟩

/-- ICARM leaderboard curve 162 has Mordell-Weil rank at least `9`. -/
public theorem curve162_hasRankGE_9 : HasRankGE curve162 9 := by
  unfold curve162
  certify_curve torsion 23 "data/curve162.txt" "data/curve162-labels.txt"

/-- Curve 162 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve162.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 162. -/
public theorem curve162_j : curve162.j = -117969718432394046233638868836 / 38564967282559125130143675 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
