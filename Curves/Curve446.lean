/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 446 has rank at least 20

The elliptic curve recorded as
[curve 446](https://elliptic-rank.icarm.cloud/curve/446) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1342601048927478697366454308878729`   and
  `a₆ = 18899547549448287969118946591445127688679527385785`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 446 over `ℚ`. -/
@[expose] public def curve446 : WeierstrassCurve ℚ :=
  ⟨1, -1, 0, -1342601048927478697366454308878729,
    18899547549448287969118946591445127688679527385785⟩

/-- ICARM leaderboard curve 446 has Mordell-Weil rank at least `20`. -/
public theorem curve446_hasRankGE_20 : HasRankGE curve446 20 := by
  unfold curve446
  certify_curve torsion 23 "data/curve446.txt" "data/curve446-labels.txt"

/-- Curve 446 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve446.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 446. -/
public theorem curve446_j : curve446.j = 367144587581216403065496262668720313173183719963491221991325537869400936618582417811879574021919892369 / 798067399066589231826704887445001106609131946651518205067083558922321326779229374240212037062500 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
