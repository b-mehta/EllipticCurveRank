/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 351 has rank at least 25

The elliptic curve recorded as
[curve 351](https://elliptic-rank.icarm.cloud/curve/351) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -250918915934128421340307896120883808444030`   and
  `a₆ = 45913507617476434834864347970127139550348536547695769941315597`

over `ℚ`. It has Mordell-Weil rank at least `25`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve351.txt`; descent labels are in
`data/curve351-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 351 over `ℚ`. -/
@[expose] public def curve351 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -250918915934128421340307896120883808444030,
    45913507617476434834864347970127139550348536547695769941315597⟩

/-- ICARM leaderboard curve 351 has Mordell-Weil rank at least `25`. -/
public theorem curve351_hasRankGE_25 : HasRankGE curve351 25 := by
  unfold curve351
  certify_curve torsion 29 "data/curve351.txt" "data/curve351-labels.txt"

/-- Curve 351 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve351.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 351. -/
public theorem curve351_j : curve351.j = 112309252177568180002603781857382227983214896036440047187363563336371039409652594226845599773437110986672531137091 / 6453296371308775174847837038234540363293732231679073439532479247235926711639788155625299374706702143920668672 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
