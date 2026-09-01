/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 31 has rank at least 10

The elliptic curve recorded as
[curve 31](https://elliptic-rank.icarm.cloud/curve/31) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2060795223235870670`   and
  `a₆ = 1037860392073475481628988676`

over `ℚ`. It has Mordell-Weil rank at least `10`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 31 over `ℚ`. -/
@[expose] public def curve031 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2060795223235870670, 1037860392073475481628988676⟩

/-- ICARM leaderboard curve 31 has Mordell-Weil rank at least `10`. -/
public theorem curve031_hasRankGE_10 : HasRankGE curve031 10 := by
  unfold curve031
  certify_curve oneTorsion 4091012848 5 "data/curve031.txt" "data/curve031-labels.txt"

/-- Curve 31 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve031.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 31. -/
public theorem curve031_j : curve031.j = 6501306190453387368858073830062529529671660018234764453 / 636725534658833049089877256511514677428219248562176 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
