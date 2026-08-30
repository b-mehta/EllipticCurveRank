/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 129 has rank at least 8

The elliptic curve recorded as
[curve 129](https://elliptic-rank.icarm.cloud/curve/129) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -481663`   and
  `a₆ = 128212738`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 129 over `ℚ`. -/
@[expose] public def curve129 : WeierstrassCurve ℚ := ⟨0, 0, 0, -481663, 128212738⟩

/-- ICARM leaderboard curve 129 has Mordell-Weil rank at least `8`. -/
public theorem curve129_hasRankGE_8 : HasRankGE curve129 8 := by
  unfold curve129
  certify_curve torsion 7 "data/curve129.txt" "data/curve129-labels.txt"

/-- Curve 129 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve129.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 129. -/
public theorem curve129_j : curve129.j = 48274035531192538704 / 196383966667225 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
