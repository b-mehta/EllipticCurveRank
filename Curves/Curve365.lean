/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 365 has rank at least 8

The elliptic curve recorded as
[curve 365](https://elliptic-rank.icarm.cloud/curve/365) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -14063345`   and
  `a₆ = 20355846671`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve365.txt`; descent labels are in
`data/curve365-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 365 over `ℚ`. -/
@[expose] public def curve365 : WeierstrassCurve ℚ := ⟨1, 1, 1, -14063345, 20355846671⟩

/-- ICARM leaderboard curve 365 has Mordell-Weil rank at least `8`. -/
public theorem curve365_hasRankGE_8 : HasRankGE curve365 8 := by
  unfold curve365
  certify_curve torsion 13 "data/curve365.txt" "data/curve365-labels.txt"

/-- Curve 365 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve365.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 365. -/
public theorem curve365_j : curve365.j = -307602320148461040768078481 / 1096203840346457653248 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
