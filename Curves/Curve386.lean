/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 386 has rank at least 20

The elliptic curve recorded as
[curve 386](https://elliptic-rank.icarm.cloud/curve/386) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1959597671778012400793716956575363`   and
  `a₆ = 31215574828451091811944359784635933468091823313217`

over `ℚ`. It has Mordell-Weil rank at least `20`.

Submitted to the leaderboard by y011d4.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 386 over `ℚ`. -/
@[expose] public def curve386 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1959597671778012400793716956575363, 31215574828451091811944359784635933468091823313217⟩

/-- ICARM leaderboard curve 386 has Mordell-Weil rank at least `20`. -/
public theorem curve386_hasRankGE_20 : HasRankGE curve386 20 := by
  unfold curve386
  certify_curve torsion 7 "data/curve386.txt" "data/curve386-labels.txt"

/-- Curve 386 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve386.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 386. -/
public theorem curve386_j : curve386.j = 53260400822714486824425942953062167195205735695126629162910366927218075658989685885351180528401056873 / 3881445147849499147057933223105448713025576988092326174222087859111706187637652890915854716502016 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
