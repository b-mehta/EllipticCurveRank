/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 372 has rank at least 8

The elliptic curve recorded as
[curve 372](https://elliptic-rank.icarm.cloud/curve/372) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -475339`   and
  `a₆ = 77898769`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by Warricker-hash.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 372 over `ℚ`. -/
@[expose] public def curve372 : WeierstrassCurve ℚ := ⟨1, -1, 0, -475339, 77898769⟩

/-- ICARM leaderboard curve 372 has Mordell-Weil rank at least `8`. -/
public theorem curve372_hasRankGE_8 : HasRankGE curve372 8 := by
  unfold curve372
  certify_curve torsion 17 "data/curve372.txt" "data/curve372-labels.txt"

/-- Curve 372 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve372.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 372. -/
public theorem curve372_j : curve372.j = 11877760680289352716041 / 4260225849214102372 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
