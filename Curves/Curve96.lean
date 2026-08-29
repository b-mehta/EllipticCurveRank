/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 96 has rank at least 17

The elliptic curve recorded as
[curve 96](https://elliptic-rank.icarm.cloud/curve/96) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -3764690650150480844855`   and
  `a₆ = 89019354183527481401653208626710`

over `ℚ`. It has Mordell-Weil rank at least `17`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve96.txt`; descent labels are in
`data/curve96-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 96 over `ℚ`. -/
@[expose] public def curve96 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -3764690650150480844855, 89019354183527481401653208626710⟩

/-- ICARM leaderboard curve 96 has Mordell-Weil rank at least `17`. -/
public theorem curve96_hasRankGE_17 : HasRankGE curve96 17 := by
  unfold curve96
  certify_curve torsion 5 "data/curve96.txt" "data/curve96-labels.txt"

/-- Curve 96 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve96.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 96. -/
public theorem curve96_j : curve96.j = -5900809556611744110592054936310452146108347243635266112400864098455913 / 8540075879702050389575912256014906231939468079986198083770051916 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
