/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 149 has rank at least 5

The elliptic curve recorded as
[curve 149](https://elliptic-rank.icarm.cloud/curve/149) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -169`   and
  `a₆ = 930`

over `ℚ`. It has Mordell-Weil rank at least `5`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve149.txt`; descent labels are in
`data/curve149-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 149 over `ℚ`. -/
@[expose] public def curve149 : WeierstrassCurve ℚ := ⟨0, 0, 1, -169, 930⟩

/-- ICARM leaderboard curve 149 has Mordell-Weil rank at least `5`. -/
public theorem curve149_hasRankGE_5 : HasRankGE curve149 5 := by
  unfold curve149
  certify_curve torsion 5 "data/curve149.txt" "data/curve149-labels.txt"

/-- Curve 149 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve149.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 149. -/
public theorem curve149_j : curve149.j = -533806460928 / 64921931 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
