/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 151 has rank at least 9

The elliptic curve recorded as
[curve 151](https://elliptic-rank.icarm.cloud/curve/151) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + a₄·x + a₆`,   with
  `a₄ = -5347108`   and
  `a₆ = 4740882532`

over `ℚ`. It has Mordell-Weil rank at least `9`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 151 over `ℚ`. -/
@[expose] public def curve151 : WeierstrassCurve ℚ := ⟨0, 0, 0, -5347108, 4740882532⟩

/-- ICARM leaderboard curve 151 has Mordell-Weil rank at least `9`. -/
public theorem curve151_hasRankGE_9 : HasRankGE curve151 9 := by
  unfold curve151
  certify_curve torsion 13 "data/curve151.txt" "data/curve151-labels.txt"

/-- Curve 151 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve151.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 151. -/
public theorem curve151_j : curve151.j = 66045101933931616963584 / 292350480654012325 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
