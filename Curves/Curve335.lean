/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 335 has rank at least 19

The elliptic curve recorded as
[curve 335](https://elliptic-rank.icarm.cloud/curve/335) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -109648466330311563423519471692`   and
  `a₆ = 14831224909223981171042503872168327240436559`

over `ℚ`. It has Mordell-Weil rank at least `19`.

Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 335 over `ℚ`. -/
@[expose] public def curve335 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -109648466330311563423519471692, 14831224909223981171042503872168327240436559⟩

/-- ICARM leaderboard curve 335 has Mordell-Weil rank at least `19`. -/
public theorem curve335_hasRankGE_19 : HasRankGE curve335 19 := by
  unfold curve335
  certify_curve torsion 7 "data/curve335.txt" "data/curve335-labels.txt"

/-- Curve 335 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve335.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 335. -/
public theorem curve335_j : curve335.j = -199987968288710035339070918772119097091746778424038342034225103645918398924732188356027769 / 14615989348765440907218560677725984426032031787567606231387690003057470444255436800000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
