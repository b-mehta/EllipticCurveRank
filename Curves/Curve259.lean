/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 259 has rank at least 8

The elliptic curve recorded as
[curve 259](https://elliptic-rank.icarm.cloud/curve/259) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -27019`   and
  `a₆ = 779689`

over `ℚ`. It has Mordell-Weil rank at least `8`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve259.txt`; descent labels are in
`data/curve259-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 259 over `ℚ`. -/
@[expose] public def curve259 : WeierstrassCurve ℚ := ⟨1, -1, 0, -27019, 779689⟩

/-- ICARM leaderboard curve 259 has Mordell-Weil rank at least `8`. -/
public theorem curve259_hasRankGE_8 : HasRankGE curve259 8 := by
  unfold curve259
  certify_curve torsion 19 "data/curve259.txt" "data/curve259-labels.txt"

/-- Curve 259 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve259.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 259. -/
public theorem curve259_j : curve259.j = 2181426413750237961 / 1004310948580012 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
