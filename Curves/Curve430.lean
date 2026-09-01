/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 430 has rank at least 20

The elliptic curve recorded as
[curve 430](https://elliptic-rank.icarm.cloud/curve/430) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -105854341112379836965356844298984005`   and
  `a₆ = 13004863393089789470296160259493256256960691084729025`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 430 over `ℚ`. -/
@[expose] public def curve430 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -105854341112379836965356844298984005,
    13004863393089789470296160259493256256960691084729025⟩

/-- ICARM leaderboard curve 430 has Mordell-Weil rank at least `20`. -/
public theorem curve430_hasRankGE_20 : HasRankGE curve430 20 := by
  unfold curve430
  certify_curve torsion 23 "data/curve430.txt" "data/curve430-labels.txt"

/-- Curve 430 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve430.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 430. -/
public theorem curve430_j : curve430.j = 131174594958797660119037487568462607587699874926895543650075832360063941404761032627813133997405360772483373521 / 2848588085384977822706970819409814653720503217702910761115999942195145917806629357405166589414891520000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
