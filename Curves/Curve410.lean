/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 410 has rank at least 21

The elliptic curve recorded as
[curve 410](https://elliptic-rank.icarm.cloud/curve/410) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -517097571914307467396942889454703`   and
  `a₆ = 4517566384703220051910945882466217158874543213431`

over `ℚ`. It has Mordell-Weil rank at least `21`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 410 over `ℚ`. -/
@[expose] public def curve410 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -517097571914307467396942889454703, 4517566384703220051910945882466217158874543213431⟩

/-- ICARM leaderboard curve 410 has Mordell-Weil rank at least `21`. -/
public theorem curve410_hasRankGE_21 : HasRankGE curve410 21 := by
  unfold curve410
  certify_curve torsion 29 "data/curve410.txt" "data/curve410-labels.txt"

/-- Curve 410 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve410.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 410. -/
public theorem curve410_j : curve410.j = 566340269937011882933773806404180363192630256043596443032182612753419719299714852487516338067311773907 / 1208715125895765758112592119807077195652728211233008756281269584810916309958369610608279433625600 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
