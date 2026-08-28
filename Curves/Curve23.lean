/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 23 has rank at least 6

The elliptic curve recorded as
[curve 23](https://elliptic-rank.icarm.cloud/curve/23) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1980651076`   and
  `a₆ = 33887665543876`

over `ℚ`. It has Mordell-Weil rank at least `6`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve23.txt`; descent labels are in
`data/curve23-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 23 over `ℚ`. -/
@[expose] public def curve23 : WeierstrassCurve ℚ := ⟨0, -1, 0, -1980651076, 33887665543876⟩

/-- ICARM leaderboard curve 23 has Mordell-Weil rank at least `6`. -/
public theorem curve23_hasRankGE_6 : HasRankGE curve23 6 := by
  unfold curve23
  certify_curve oneTorsion 99844 29 "data/curve23.txt" "data/curve23-labels.txt"

/-- Curve 23 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve23.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 23. -/
public theorem curve23_j : curve23.j = 3356662445517276992391469247824 / 4707582391854002335700025 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
