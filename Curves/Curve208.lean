/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 208 has rank at least 12

The elliptic curve recorded as
[curve 208](https://elliptic-rank.icarm.cloud/curve/208) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -304695382156188407658584613236`   and
  `a₆ = 64760983700857400691050362439563148137462416`

over `ℚ`. It has Mordell-Weil rank at least `12`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve208.txt`; descent labels are in
`data/curve208-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 208 over `ℚ`. -/
@[expose] public def curve208 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -304695382156188407658584613236, 64760983700857400691050362439563148137462416⟩

/-- ICARM leaderboard curve 208 has Mordell-Weil rank at least `12`. -/
public theorem curve208_hasRankGE_12 : HasRankGE curve208 12 := by
  unfold curve208
  certify_curve torsion 13 "data/curve208.txt" "data/curve208-labels.txt"

/-- Curve 208 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve208.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 208. -/
public theorem curve208_j : curve208.j = -3128393169286630462520328777905373459306995084459718865021587641478730111447962653155468116289 / 1388810570434782811007607331048073936871115674258540673227450623892810201037842324019200 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
