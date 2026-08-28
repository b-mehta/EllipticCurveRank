/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 211 has rank at least 15

The elliptic curve recorded as
[curve 211](https://elliptic-rank.icarm.cloud/curve/211) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -2164487921238768499500640803351`   and
  `a₆ = 1226101128097099442256424377019056466085320681`

over `ℚ`. It has Mordell-Weil rank at least `15`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve211.txt`; descent labels are in
`data/curve211-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 211 over `ℚ`. -/
@[expose] public def curve211 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -2164487921238768499500640803351, 1226101128097099442256424377019056466085320681⟩

/-- ICARM leaderboard curve 211 has Mordell-Weil rank at least `15`. -/
public theorem curve211_hasRankGE_15 : HasRankGE curve211 15 := by
  unfold curve211
  certify_curve torsion 41 "data/curve211.txt" "data/curve211-labels.txt"

/-- Curve 211 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve211.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 211. -/
public theorem curve211_j : curve211.j = -232342735430301956383814966432094438636510738784036341850483988983724892900248634587418361 / 90079517350164642633699417133965856976191879492333934655832670018767773499956428800 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
