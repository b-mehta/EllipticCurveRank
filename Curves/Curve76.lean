/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 76 has rank at least 8

The elliptic curve recorded as
[curve 76](https://elliptic-rank.icarm.cloud/curve/76) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -23737`   and
  `a₆ = 960366`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve76.txt`; descent labels are in
`data/curve76-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 76 over `ℚ`. -/
@[expose] public def curve76 : WeierstrassCurve ℚ := ⟨0, 0, 1, -23737, 960366⟩

/-- ICARM leaderboard curve 76 has Mordell-Weil rank at least `8`. -/
public theorem curve76_hasRankGE_8 : HasRankGE curve76 8 := by
  unfold curve76
  certify_curve torsion 7 "data/curve76.txt" "data/curve76-labels.txt"

/-- Curve 76 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve76.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 76. -/
public theorem curve76_j : curve76.j = 1479112480222949376 / 457532830151317 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
