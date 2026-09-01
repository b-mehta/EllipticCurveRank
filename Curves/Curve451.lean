/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 451 has rank at least 20

The elliptic curve recorded as
[curve 451](https://elliptic-rank.icarm.cloud/curve/451) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -125314579511982544183702370268945`   and
  `a₆ = 515796522496291694328940607345967092483061434025`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 451 over `ℚ`. -/
@[expose] public def curve451 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -125314579511982544183702370268945, 515796522496291694328940607345967092483061434025⟩

/-- ICARM leaderboard curve 451 has Mordell-Weil rank at least `20`. -/
public theorem curve451_hasRankGE_20 : HasRankGE curve451 20 := by
  unfold curve451
  certify_curve torsion 71 "data/curve451.txt" "data/curve451-labels.txt"

/-- Curve 451 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve451.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 451. -/
public theorem curve451_j : curve451.j = 217634887713233906213513249571547753708877314198899794095382291810782546704512126114667690257191412881 / 11014220843264556546447448734799935278705945925559546130402155148854354537539562363089294950400000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
