/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 321 has rank at least 19

The elliptic curve recorded as
[curve 321](https://elliptic-rank.icarm.cloud/curve/321) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -252160457594955208636121130356708`   and
  `a₆ = 1519947879571352753434584073837249656547139834631`

over `ℚ`. It has Mordell-Weil rank at least `19`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 321 over `ℚ`. -/
@[expose] public def curve321 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -252160457594955208636121130356708, 1519947879571352753434584073837249656547139834631⟩

/-- ICARM leaderboard curve 321 has Mordell-Weil rank at least `19`. -/
public theorem curve321_hasRankGE_19 : HasRankGE curve321 19 := by
  unfold curve321
  certify_curve torsion 41 "data/curve321.txt" "data/curve321-labels.txt"

/-- Curve 321 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve321.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 321. -/
public theorem curve321_j : curve321.j = 2432355982741204140180119484645833066243102245039412963258124826823616639626444491847402864366352121 / 38581382389484981905877526170097098387179468201927839318828444243965095303055553754601550643200 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
