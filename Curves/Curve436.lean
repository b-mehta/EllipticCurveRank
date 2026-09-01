/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 436 has rank at least 20

The elliptic curve recorded as
[curve 436](https://elliptic-rank.icarm.cloud/curve/436) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -85662285878324393186410215408681700`   and
  `a₆ = 9305394083127186081227398401022012428368804281129232`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 436 over `ℚ`. -/
@[expose] public def curve436 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -85662285878324393186410215408681700,
    9305394083127186081227398401022012428368804281129232⟩

/-- ICARM leaderboard curve 436 has Mordell-Weil rank at least `20`. -/
public theorem curve436_hasRankGE_20 : HasRankGE curve436 20 := by
  unfold curve436
  certify_curve torsion 23 "data/curve436.txt" "data/curve436-labels.txt"

/-- Curve 436 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve436.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 436. -/
public theorem curve436_j : curve436.j = 37092473377205809136754867385882856006873137667436126120019162715319888313796244524230411789158789852241 / 1506201855820602126732444933778029968910725481409011084966031328591413188643208889169684094976000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
