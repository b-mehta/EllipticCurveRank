/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 413 has rank at least 24

The elliptic curve recorded as
[curve 413](https://elliptic-rank.icarm.cloud/curve/413) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -6128282860470603511303288155661829055`   and
  `a₆ = 5852434608243230932760773539506370894306070621155215001`

over `ℚ`. It has Mordell-Weil rank at least `24`. Submitted to the leaderboard by Rayan Hatout.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 413 over `ℚ`. -/
@[expose] public def curve413 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -6128282860470603511303288155661829055,
    5852434608243230932760773539506370894306070621155215001⟩

/-- ICARM leaderboard curve 413 has Mordell-Weil rank at least `24`. -/
public theorem curve413_hasRankGE_24 : HasRankGE curve413 24 := by
  unfold curve413
  certify_curve torsion 19 "data/curve413.txt" "data/curve413-labels.txt"

/-- Curve 413 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve413.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 413. -/
public theorem curve413_j : curve413.j = -25453066959687229067792565679700342913981744261462516558186273119854093935838480778483290886357697651826089590916721 / 66643924316290495097031601682555186588559481494004949405963419708479467342166011289207729989773885624388026368 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
