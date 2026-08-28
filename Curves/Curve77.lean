/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 77 has rank at least 8

The elliptic curve recorded as
[curve 77](https://elliptic-rank.icarm.cloud/curve/77) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -222751`   and
  `a₆ = 40537273`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve77.txt`; descent labels are in
`data/curve77-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 77 over `ℚ`. -/
@[expose] public def curve77 : WeierstrassCurve ℚ := ⟨1, -1, 0, -222751, 40537273⟩

/-- ICARM leaderboard curve 77 has Mordell-Weil rank at least `8`. -/
public theorem curve77_hasRankGE_8 : HasRankGE curve77 8 := by
  unfold curve77
  certify_curve torsion 5 "data/curve77.txt" "data/curve77-labels.txt"

/-- Curve 77 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve77.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 77. -/
public theorem curve77_j : curve77.j = -1222316842517959109193 / 584492602941116 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
