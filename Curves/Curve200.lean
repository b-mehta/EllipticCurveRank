/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 200 has rank at least 13

The elliptic curve recorded as
[curve 200](https://elliptic-rank.icarm.cloud/curve/200) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -1213916060668229132`   and
  `a₆ = 555373168020983867224329231`

over `ℚ`. It has Mordell-Weil rank at least `13`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve200.txt`; descent labels are in
`data/curve200-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 200 over `ℚ`. -/
@[expose] public def curve200 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -1213916060668229132, 555373168020983867224329231⟩

/-- ICARM leaderboard curve 200 has Mordell-Weil rank at least `13`. -/
public theorem curve200_hasRankGE_13 : HasRankGE curve200 13 := by
  unfold curve200
  certify_curve torsion 13 "data/curve200.txt" "data/curve200-labels.txt"

/-- Curve 200 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve200.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 200. -/
public theorem curve200_j : curve200.j = -271370200755167236286666501124558324998839548306523308409 / 25735937034434233705743782154153422636662996992000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
