/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 217 has rank at least 16

The elliptic curve recorded as
[curve 217](https://elliptic-rank.icarm.cloud/curve/217) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -5392334889373133836717`   and
  `a₆ = 152408175069865597518128713267441`

over `ℚ`. It has Mordell-Weil rank at least `16`. Submitted to the leaderboard by Edgar Costa.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 217 over `ℚ`. -/
@[expose] public def curve217 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -5392334889373133836717, 152408175069865597518128713267441⟩

/-- ICARM leaderboard curve 217 has Mordell-Weil rank at least `16`. -/
public theorem curve217_hasRankGE_16 : HasRankGE curve217 16 := by
  unfold curve217
  certify_curve torsion 7 "data/curve217.txt" "data/curve217-labels.txt"

/-- Curve 217 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve217.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 217. -/
public theorem curve217_j : curve217.j = 1109773255208910277577034518246441221406516454134412700698782845473 / 15186528023219984188634768546364937506656281214045339786116 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
