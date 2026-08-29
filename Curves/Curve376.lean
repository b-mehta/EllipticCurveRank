/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 376 has rank at least 22

The elliptic curve recorded as
[curve 376](https://elliptic-rank.icarm.cloud/curve/376) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -1445990013167463346228809073545620`   and
  `a₆ = 21128721995181552195912389455017474056877615305616`

over `ℚ`. It has Mordell-Weil rank at least `22`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve376.txt`; descent labels are in
`data/curve376-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 376 over `ℚ`. -/
@[expose] public def curve376 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -1445990013167463346228809073545620, 21128721995181552195912389455017474056877615305616⟩

/-- ICARM leaderboard curve 376 has Mordell-Weil rank at least `22`. -/
public theorem curve376_hasRankGE_22 : HasRankGE curve376 22 := by
  unfold curve376
  certify_curve torsion 41 "data/curve376.txt" "data/curve376-labels.txt"

/-- Curve 376 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve376.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 376. -/
public theorem curve376_j : curve376.j = 334364061990168950216052472111017193393081668741632097322283208281643833395315662289545187674276235318081 / 643031218468664206983673895482549260328406935268474125048298063324864932907314896916917745512087552 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
