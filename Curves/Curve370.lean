/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 370 has rank at least 10

The elliptic curve recorded as
[curve 370](https://elliptic-rank.icarm.cloud/curve/370) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -49868394`   and
  `a₆ = 160512600824`

over `ℚ`. It has Mordell-Weil rank at least `10`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve370.txt`; descent labels are in
`data/curve370-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 370 over `ℚ`. -/
@[expose] public def curve370 : WeierstrassCurve ℚ := ⟨1, -1, 0, -49868394, 160512600824⟩

/-- ICARM leaderboard curve 370 has Mordell-Weil rank at least `10`. -/
public theorem curve370_hasRankGE_10 : HasRankGE curve370 10 := by
  unfold curve370
  certify_curve torsion 7 "data/curve370.txt" "data/curve370-labels.txt"

/-- Curve 370 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve370.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 370. -/
public theorem curve370_j : curve370.j = -6271206192181504179256203 / 1459282673528217427324 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
