/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 22 has rank at least 6

The elliptic curve recorded as
[curve 22](https://elliptic-rank.icarm.cloud/curve/22) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1664597956`   and
  `a₆ = 26095909440100`

over `ℚ`. It has Mordell-Weil rank at least `6`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 22 over `ℚ`. -/
@[expose] public def curve22 : WeierstrassCurve ℚ := ⟨0, -1, 0, -1664597956, 26095909440100⟩

/-- ICARM leaderboard curve 22 has Mordell-Weil rank at least `6`. -/
public theorem curve22_hasRankGE_6 : HasRankGE curve22 6 := by
  unfold curve22
  certify_curve oneTorsion 91012 29 "data/curve22.txt" "data/curve22-labels.txt"

/-- Curve 22 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve22.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 22. -/
public theorem curve22_j : curve22.j = 1992561882830305777698340062544 / 3970233989185030110569025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
