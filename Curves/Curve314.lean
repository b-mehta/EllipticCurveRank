/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 314 has rank at least 18

The elliptic curve recorded as
[curve 314](https://elliptic-rank.icarm.cloud/curve/314) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -5259979010001805005968016`   and
  `a₆ = 4642551389959286676185695447422235620`

over `ℚ`. It has Mordell-Weil rank at least `18`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve314.txt`; descent labels are in
`data/curve314-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 314 over `ℚ`. -/
@[expose] public def curve314 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -5259979010001805005968016, 4642551389959286676185695447422235620⟩

/-- ICARM leaderboard curve 314 has Mordell-Weil rank at least `18`. -/
public theorem curve314_hasRankGE_18 : HasRankGE curve314 18 := by
  unfold curve314
  certify_curve torsion 53 "data/curve314.txt" "data/curve314-labels.txt"

/-- Curve 314 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve314.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 314. -/
public theorem curve314_j : curve314.j = 3256234511881381202582946155479610758095647517993453099154019100371044 / 584894329685105882822674762285393950267849659547324769418149425 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
