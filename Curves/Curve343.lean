/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 343 has rank at least 19

The elliptic curve recorded as
[curve 343](https://elliptic-rank.icarm.cloud/curve/343) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -43285881523530475258933144164152`   and
  `a₆ = 109614989666789360127642358536641482836869473979`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve343.txt`; descent labels are in
`data/curve343-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 343 over `ℚ`. -/
@[expose] public def curve343 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -43285881523530475258933144164152, 109614989666789360127642358536641482836869473979⟩

/-- ICARM leaderboard curve 343 has Mordell-Weil rank at least `19`. -/
public theorem curve343_hasRankGE_19 : HasRankGE curve343 19 := by
  unfold curve343
  certify_curve torsion 7 "data/curve343.txt" "data/curve343-labels.txt"

/-- Curve 343 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve343.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 343. -/
public theorem curve343_j : curve343.j = -12303678747577894956495860988196031421194909656265796373994636229968444608792843000468387839619129 / 79811981509795663078534619805998676840211162357622322656498746828513443686280011228160000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
