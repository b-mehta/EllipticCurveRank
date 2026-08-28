/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 213 has rank at least 16

The elliptic curve recorded as
[curve 213](https://elliptic-rank.icarm.cloud/curve/213) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -74540773450198004669118078904466`   and
  `a₆ = 244066692939635107384386902977544619850388014596`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve213.txt`; descent labels are in
`data/curve213-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 213 over `ℚ`. -/
@[expose] public def curve213 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -74540773450198004669118078904466, 244066692939635107384386902977544619850388014596⟩

/-- ICARM leaderboard curve 213 has Mordell-Weil rank at least `16`. -/
public theorem curve213_hasRankGE_16 : HasRankGE curve213 16 := by
  unfold curve213
  certify_curve torsion 13 "data/curve213.txt" "data/curve213-labels.txt"

/-- Curve 213 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve213.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 213. -/
public theorem curve213_j : curve213.j = 9323063286604025284879916886792999388650720352880404671872534698286462581334808447986723089284593 / 157429690565975543132692704081228907283208332626470792750880645512928036152258726661904793600 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
