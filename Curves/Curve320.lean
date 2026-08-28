/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 320 has rank at least 19

The elliptic curve recorded as
[curve 320](https://elliptic-rank.icarm.cloud/curve/320) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -3487873891980168936388181335535`   and
  `a₆ = 2444345666762251558502690972431521736588391097`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve320.txt`; descent labels are in
`data/curve320-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 320 over `ℚ`. -/
@[expose] public def curve320 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -3487873891980168936388181335535, 2444345666762251558502690972431521736588391097⟩

/-- ICARM leaderboard curve 320 has Mordell-Weil rank at least `19`. -/
public theorem curve320_hasRankGE_19 : HasRankGE curve320 19 := by
  unfold curve320
  certify_curve torsion 53 "data/curve320.txt" "data/curve320-labels.txt"

/-- Curve 320 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve320.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 320. -/
public theorem curve320_j : curve320.j = 4692518943631032253549987531094120939317933523172612824300708916123664522756677504453734707536241 / 134453373295489843369140613497101086804354919153960791684931108232412909602091138560000000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
