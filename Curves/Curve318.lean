/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 318 has rank at least 15

The elliptic curve recorded as
[curve 318](https://elliptic-rank.icarm.cloud/curve/318) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -107404730164187455100283304999195859754632145403`   and
  `a₆ = 48976939778870435455584633601954124477725966045276826839333933204370006`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by Jack Cheng.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 318 over `ℚ`. -/
@[expose] public def curve318 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -107404730164187455100283304999195859754632145403,
    48976939778870435455584633601954124477725966045276826839333933204370006⟩

/-- ICARM leaderboard curve 318 has Mordell-Weil rank at least `15`. -/
public theorem curve318_hasRankGE_15 : HasRankGE curve318 15 := by
  unfold curve318
  certify_curve torsion 31 "data/curve318.txt" "data/curve318-labels.txt"

/-- Curve 318 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve318.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 318. -/
public theorem curve318_j : curve318.j = -137023146838625771995638221687709925847219401141465730162865623322574727782279040154802710191592940279456489296834252868755267093480577514413493161 / 956960149635890553026355922064884560686815442397416962941379345991616974205586950201323526133577691235859622088389207804542013981650254781250000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
