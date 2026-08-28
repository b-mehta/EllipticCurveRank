/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 338 has rank at least 19

The elliptic curve recorded as
[curve 338](https://elliptic-rank.icarm.cloud/curve/338) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -855631467438096021846442064975`   and
  `a₆ = 305451237205254133961575716954767187528207317`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve338.txt`; descent labels are in
`data/curve338-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 338 over `ℚ`. -/
@[expose] public def curve338 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -855631467438096021846442064975, 305451237205254133961575716954767187528207317⟩

/-- ICARM leaderboard curve 338 has Mordell-Weil rank at least `19`. -/
public theorem curve338_hasRankGE_19 : HasRankGE curve338 19 := by
  unfold curve338
  certify_curve torsion 17 "data/curve338.txt" "data/curve338-labels.txt"

/-- Curve 338 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve338.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 338. -/
public theorem curve338_j : curve338.j = -2425551764262394578376210083439778033096264455863384165821338425638317710470891629249321441 / 7542234725679310964830423327022872806287816768082737256408930544961065899176755200000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
