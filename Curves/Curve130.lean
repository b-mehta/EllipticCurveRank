/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 130 has rank at least 8

The elliptic curve recorded as
[curve 130](https://elliptic-rank.icarm.cloud/curve/130) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -71899`   and
  `a₆ = 5522449`

over `ℚ`. It has Mordell-Weil rank at least `8`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 130 over `ℚ`. -/
@[expose] public def curve130 : WeierstrassCurve ℚ := ⟨1, -1, 0, -71899, 5522449⟩

/-- ICARM leaderboard curve 130 has Mordell-Weil rank at least `8`. -/
public theorem curve130_hasRankGE_8 : HasRankGE curve130 8 := by
  unfold curve130
  certify_curve torsion 7 "data/curve130.txt" "data/curve130-labels.txt"

/-- Curve 130 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve130.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 130. -/
public theorem curve130_j : curve130.j = 41105095360047286281 / 10698400790403652 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
