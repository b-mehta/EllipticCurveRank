/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 417 has rank at least 26

The elliptic curve recorded as
[curve 417](https://elliptic-rank.icarm.cloud/curve/417) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -90727410878564661344565489473501960846232523437`   and
  `a₆ = 12098701628080370470556151946562046635806600287349459526333680614637461`

over `ℚ`. It has Mordell-Weil rank at least `26`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 417 over `ℚ`. -/
@[expose] public def curve417 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -90727410878564661344565489473501960846232523437,
    12098701628080370470556151946562046635806600287349459526333680614637461⟩

/-- ICARM leaderboard curve 417 has Mordell-Weil rank at least `26`. -/
public theorem curve417_hasRankGE_26 : HasRankGE curve417 26 := by
  unfold curve417
  certify_curve torsion 19 "data/curve417.txt" "data/curve417-labels.txt"

/-- Curve 417 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve417.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 417. -/
public theorem curve417_j : curve417.j = -82592243721567485758903882714385160008491474055262450350926196526905006139843174429504319401804612754063082442167849184625944499671995279088315681 / 15439109689985837477065269882391384566307066564733753168278692405867817968998372518404179248111503571943794320665209194237939134339960000000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
