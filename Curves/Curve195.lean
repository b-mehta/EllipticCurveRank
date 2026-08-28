/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 195 has rank at least 14

The elliptic curve recorded as
[curve 195](https://elliptic-rank.icarm.cloud/curve/195) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -54431691335588366573`   and
  `a₆ = 180548233661579697703929158997`

over `ℚ`. It has Mordell-Weil rank at least `14`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve195.txt`; descent labels are in
`data/curve195-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 195 over `ℚ`. -/
@[expose] public def curve195 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -54431691335588366573, 180548233661579697703929158997⟩

/-- ICARM leaderboard curve 195 has Mordell-Weil rank at least `14`. -/
public theorem curve195_hasRankGE_14 : HasRankGE curve195 14 := by
  unfold curve195
  certify_curve torsion 17 "data/curve195.txt" "data/curve195-labels.txt"

/-- Curve 195 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve195.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 195. -/
public theorem curve195_j : curve195.j = -24465363422306590661135141460429292025703338808351258813588361 / 5158938196329675526322265643855564006774286292760176230400 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
