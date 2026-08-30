/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 363 has rank at least 27

The elliptic curve recorded as
[curve 363](https://elliptic-rank.icarm.cloud/curve/363) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -77784861105517331567918462464043246062399071551`   and
  `a₆ = 9729372994024391552036598189578155261901018816064506695929640000090598`

over `ℚ`. It has Mordell-Weil rank at least `27`.

Submitted to the leaderboard by wgxli.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 363 over `ℚ`. -/
@[expose] public def curve363 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -77784861105517331567918462464043246062399071551,
    9729372994024391552036598189578155261901018816064506695929640000090598⟩

/-- ICARM leaderboard curve 363 has Mordell-Weil rank at least `27`. -/
public theorem curve363_hasRankGE_27 : HasRankGE curve363 27 := by
  unfold curve363
  certify_curve torsion 23 "data/curve363.txt" "data/curve363-labels.txt"

/-- Curve 363 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve363.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 363. -/
public theorem curve363_j : curve363.j = -83277741099574437456360812462151261620373083507397416185399646493209966214635816415464605172252250521953434055047012569549827205888704014040825 / 17236337839453643461095458315910737430544703958958214003704028337735401916228364928402680460043728234144587145925770595573562378778345224452 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
