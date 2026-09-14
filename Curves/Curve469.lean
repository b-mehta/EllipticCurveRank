/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 469 has rank at least 8

The elliptic curve recorded as
[curve 469](https://elliptic-rank.icarm.cloud/curve/469) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -14856176`   and
  `a₆ = 21132808740`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 469 over `ℚ`. -/
@[expose] public def curve469 : WeierstrassCurve ℚ := ⟨0, 1, 0, -14856176, 21132808740⟩

/-- ICARM leaderboard curve 469 has Mordell-Weil rank at least `8`. -/
public theorem curve469_hasRankGE_8 : HasRankGE curve469 8 := by
  unfold curve469
  certify_curve torsion 11 "data/curve469.txt" "data/curve469-labels.txt"

/-- Curve 469 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve469.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 469. -/
public theorem curve469_j : curve469.j = 354115463697841188399556 / 16432099868365733025 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
