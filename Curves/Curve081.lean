/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 81 has rank at least 9

The elliptic curve recorded as
[curve 81](https://elliptic-rank.icarm.cloud/curve/81) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -826609`   and
  `a₆ = 289956150`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 81 over `ℚ`. -/
@[expose] public def curve081 : WeierstrassCurve ℚ := ⟨0, 0, 1, -826609, 289956150⟩

/-- ICARM leaderboard curve 81 has Mordell-Weil rank at least `9`. -/
public theorem curve081_hasRankGE_9 : HasRankGE curve081 9 := by
  unfold curve081
  certify_curve torsion 5 "data/curve081.txt" "data/curve081-labels.txt"

/-- Curve 81 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve081.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 81. -/
public theorem curve081_j : curve081.j = -62463181476112721031168 / 172539371946838571 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
