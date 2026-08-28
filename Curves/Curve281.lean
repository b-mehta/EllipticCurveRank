/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 281 has rank at least 19

The elliptic curve recorded as
[curve 281](https://elliptic-rank.icarm.cloud/curve/281) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -26209631133105489807468060702`   and
  `a₆ = 1629345706371694346940183718532493403517124`

over `ℚ`. It has Mordell-Weil rank at least `19`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve281.txt`; descent labels are in
`data/curve281-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 281 over `ℚ`. -/
@[expose] public def curve281 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -26209631133105489807468060702, 1629345706371694346940183718532493403517124⟩

/-- ICARM leaderboard curve 281 has Mordell-Weil rank at least `19`. -/
public theorem curve281_hasRankGE_19 : HasRankGE curve281 19 := by
  unfold curve281
  certify_curve torsion 5 "data/curve281.txt" "data/curve281-labels.txt"

/-- Curve 281 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve281.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 281. -/
public theorem curve281_j : curve281.j = 1991161281218193546356044300569933537573823853021873343638659072525730123754723003730459873 / 5432877975727185226735785866014954478423233775179229622774668572659776350389518843904 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
