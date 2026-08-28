/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 169 has rank at least 16

The elliptic curve recorded as
[curve 169](https://elliptic-rank.icarm.cloud/curve/169) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -12539168820487782745280`   and
  `a₆ = 540409134152049294268977949499028`

over `ℚ`. It has Mordell-Weil rank at least `16`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve169.txt`; descent labels are in
`data/curve169-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 169 over `ℚ`. -/
@[expose] public def curve169 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -12539168820487782745280, 540409134152049294268977949499028⟩

/-- ICARM leaderboard curve 169 has Mordell-Weil rank at least `16`. -/
public theorem curve169_hasRankGE_16 : HasRankGE curve169 16 := by
  unfold curve169
  certify_curve torsion 19 "data/curve169.txt" "data/curve169-labels.txt"

/-- Curve 169 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve169.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 169. -/
public theorem curve169_j : curve169.j = 106463320761510300047071252938724835443534285780386651752594533856642 / 8101849327528645970243617259573240593339846410569575171171875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
