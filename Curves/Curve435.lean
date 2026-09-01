/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 435 has rank at least 20

The elliptic curve recorded as
[curve 435](https://elliptic-rank.icarm.cloud/curve/435) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -491207823564768633438000932167842220`   and
  `a₆ = 134132256298970127093936962644107344568006870419584400`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 435 over `ℚ`. -/
@[expose] public def curve435 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -491207823564768633438000932167842220,
    134132256298970127093936962644107344568006870419584400⟩

/-- ICARM leaderboard curve 435 has Mordell-Weil rank at least `20`. -/
public theorem curve435_hasRankGE_20 : HasRankGE curve435 20 := by
  unfold curve435
  certify_curve torsion 17 "data/curve435.txt" "data/curve435-labels.txt"

/-- Curve 435 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve435.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 435. -/
public theorem curve435_j : curve435.j = -13107490088203540540664008957764645354162841656295987759991794751170264840011129225126593752743482956043625996481 / 186958601393353252327110498841398254188347817102394513204661439461977075991984262361321535370901510400000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
