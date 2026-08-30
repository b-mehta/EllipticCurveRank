/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 47 has rank at least 8

The elliptic curve recorded as
[curve 47](https://elliptic-rank.icarm.cloud/curve/47) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -106384`   and
  `a₆ = 13075804`

over `ℚ`. It has Mordell-Weil rank at least `8`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 47 over `ℚ`. -/
@[expose] public def curve47 : WeierstrassCurve ℚ := ⟨1, -1, 0, -106384, 13075804⟩

/-- ICARM leaderboard curve 47 has Mordell-Weil rank at least `8`. -/
public theorem curve47_hasRankGE_8 : HasRankGE curve47 8 := by
  unfold curve47
  certify_curve torsion 53 "data/curve47.txt" "data/curve47-labels.txt"

/-- Curve 47 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve47.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

/-- The `j`-invariant of curve 47. -/
public theorem curve47_j : curve47.j = 133154226240373724121 / 3495093928855732 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
