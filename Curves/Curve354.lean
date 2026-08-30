/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 354 has rank at least 8

The elliptic curve recorded as
[curve 354](https://elliptic-rank.icarm.cloud/curve/354) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1339654280`   and
  `a₆ = 18843018310347`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 354 over `ℚ`. -/
@[expose] public def curve354 : WeierstrassCurve ℚ := ⟨1, -1, 1, -1339654280, 18843018310347⟩

/-- ICARM leaderboard curve 354 has Mordell-Weil rank at least `8`. -/
public theorem curve354_hasRankGE_8 : HasRankGE curve354 8 := by
  unfold curve354
  certify_curve torsion 7 "data/curve354.txt" "data/curve354-labels.txt"

/-- Curve 354 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve354.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 354. -/
public theorem curve354_j : curve354.j = 23342876121715006911992497 / 43133355126662221824 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
