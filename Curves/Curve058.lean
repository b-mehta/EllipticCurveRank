/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 58 has rank at least 8

The elliptic curve recorded as
[curve 58](https://elliptic-rank.icarm.cloud/curve/58) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -16440`   and
  `a₆ = 1394010`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 58 over `ℚ`. -/
@[expose] public def curve058 : WeierstrassCurve ℚ := ⟨0, 1, 1, -16440, 1394010⟩

/-- ICARM leaderboard curve 58 has Mordell-Weil rank at least `8`. -/
public theorem curve058_hasRankGE_8 : HasRankGE curve058 8 := by
  unfold curve058
  certify_curve torsion 31 "data/curve058.txt" "data/curve058-labels.txt"

/-- Curve 58 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve058.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 58. -/
public theorem curve058_j : curve058.j = -491423101350547456 / 561715239383323 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
