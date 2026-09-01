/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 25 has rank at least 6

The elliptic curve recorded as
[curve 25](https://elliptic-rank.icarm.cloud/curve/25) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -3002115396`   and
  `a₆ = 63280268148996`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 25 over `ℚ`. -/
@[expose] public def curve025 : WeierstrassCurve ℚ := ⟨0, -1, 0, -3002115396, 63280268148996⟩

/-- ICARM leaderboard curve 25 has Mordell-Weil rank at least `6`. -/
public theorem curve025_hasRankGE_6 : HasRankGE curve025 6 := by
  unfold curve025
  certify_curve oneTorsion 124164 29 "data/curve025.txt" "data/curve025-labels.txt"

/-- Curve 25 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve025.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 25. -/
public theorem curve025_j : curve025.j = 11688691385338998159136562388304 / 7090647253657448221766025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
