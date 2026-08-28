/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 315 has rank at least 10

The elliptic curve recorded as
[curve 315](https://elliptic-rank.icarm.cloud/curve/315) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -8110664060`   and
  `a₆ = 287282774486064`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve315.txt`; descent labels are in
`data/curve315-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 315 over `ℚ`. -/
@[expose] public def curve315 : WeierstrassCurve ℚ := ⟨0, 1, 0, -8110664060, 287282774486064⟩

/-- ICARM leaderboard curve 315 has Mordell-Weil rank at least `10`. -/
public theorem curve315_hasRankGE_10 : HasRankGE curve315 10 := by
  unfold curve315
  certify_curve torsion 11 "data/curve315.txt" "data/curve315-labels.txt"

/-- Curve 315 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve315.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 315. -/
public theorem curve315_j : curve315.j = -230490477355906981928446842651856 / 5888653280312743913352137523 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
