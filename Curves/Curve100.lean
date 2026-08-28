/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 100 has rank at least 10

The elliptic curve recorded as
[curve 100](https://elliptic-rank.icarm.cloud/curve/100) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + y = x³ + a₄·x + a₆`,   with
  `a₄ = -21078967`   and
  `a₆ = 35688990786`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve100.txt`; descent labels are in
`data/curve100-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 100 over `ℚ`. -/
@[expose] public def curve100 : WeierstrassCurve ℚ := ⟨0, 0, 1, -21078967, 35688990786⟩

/-- ICARM leaderboard curve 100 has Mordell-Weil rank at least `10`. -/
public theorem curve100_hasRankGE_10 : HasRankGE curve100 10 := by
  unfold curve100
  certify_curve torsion 7 "data/curve100.txt" "data/curve100-labels.txt"

/-- Curve 100 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve100.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 100. -/
public theorem curve100_j : curve100.j = 1035789928760181405862711296 / 49175312669184233794357 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
