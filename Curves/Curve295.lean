/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 295 has rank at least 19

The elliptic curve recorded as
[curve 295](https://elliptic-rank.icarm.cloud/curve/295) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -17376238614102880805191699606601`   and
  `a₆ = 27567969093931513230545328071325120978929115848`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve295.txt`; descent labels are in
`data/curve295-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 295 over `ℚ`. -/
@[expose] public def curve295 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -17376238614102880805191699606601, 27567969093931513230545328071325120978929115848⟩

/-- ICARM leaderboard curve 295 has Mordell-Weil rank at least `19`. -/
public theorem curve295_hasRankGE_19 : HasRankGE curve295 19 := by
  unfold curve295
  certify_curve torsion 7 "data/curve295.txt" "data/curve295-labels.txt"

/-- Curve 295 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve295.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 295. -/
public theorem curve295_j : curve295.j = 37133937440760654537599172540876847875891814771495161816699708393961419524003006236874613849217 / 477262878906169271744832626842481785809462502498655456840888464755966156909786140405551764 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
