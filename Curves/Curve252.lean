/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 252 has rank at least 6

The elliptic curve recorded as
[curve 252](https://elliptic-rank.icarm.cloud/curve/252) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -2093345`   and
  `a₆ = 1165078600`

over `ℚ`. It has Mordell-Weil rank at least `6`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 252 over `ℚ`. -/
@[expose] public def curve252 : WeierstrassCurve ℚ := ⟨0, 1, 0, -2093345, 1165078600⟩

/-- ICARM leaderboard curve 252 has Mordell-Weil rank at least `6`. -/
public theorem curve252_hasRankGE_6 : HasRankGE curve252 6 := by
  unfold curve252
  certify_curve torsion 17 "data/curve252.txt" "data/curve252-labels.txt"

/-- Curve 252 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve252.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 252. -/
public theorem curve252_j : curve252.j = -63405417311133871783936 / 983617230296875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
