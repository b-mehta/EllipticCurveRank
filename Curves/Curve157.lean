/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 157 has rank at least 12

The elliptic curve recorded as
[curve 157](https://elliptic-rank.icarm.cloud/curve/157) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -227292004`   and
  `a₆ = 882331831684`

over `ℚ`. It has Mordell-Weil rank at least `12`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve157.txt`; descent labels are in
`data/curve157-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 157 over `ℚ`. -/
@[expose] public def curve157 : WeierstrassCurve ℚ := ⟨1, -1, 0, -227292004, 882331831684⟩

/-- ICARM leaderboard curve 157 has Mordell-Weil rank at least `12`. -/
public theorem curve157_hasRankGE_12 : HasRankGE curve157 12 := by
  unfold curve157
  certify_curve torsion 7 "data/curve157.txt" "data/curve157-labels.txt"

/-- Curve 157 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve157.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 157. -/
public theorem curve157_j : curve157.j = 1298602356131335025937045368601 / 415233222642657545546160892 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
