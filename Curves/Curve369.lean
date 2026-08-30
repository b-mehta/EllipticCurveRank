/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 369 has rank at least 8

The elliptic curve recorded as
[curve 369](https://elliptic-rank.icarm.cloud/curve/369) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -2360940`   and
  `a₆ = 1452162276`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 369 over `ℚ`. -/
@[expose] public def curve369 : WeierstrassCurve ℚ := ⟨0, -1, 0, -2360940, 1452162276⟩

/-- ICARM leaderboard curve 369 has Mordell-Weil rank at least `8`. -/
public theorem curve369_hasRankGE_8 : HasRankGE curve369 8 := by
  unfold curve369
  certify_curve torsion 11 "data/curve369.txt" "data/curve369-labels.txt"

/-- Curve 369 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve369.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 369. -/
public theorem curve369_j : curve369.j = -5685108812391047578576 / 264708770551352883 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
