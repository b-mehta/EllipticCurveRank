/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 7 has rank at least 20

The elliptic curve recorded as
[curve 7](https://elliptic-rank.icarm.cloud/curve/7) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -431092980766333677958362095891166`   and
  `a₆ = 5156283555366643659035652799871176909391533088196`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 7, Nagao's rank-20 curve over `ℚ`. -/
@[expose] public def curve007 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -431092980766333677958362095891166, 5156283555366643659035652799871176909391533088196⟩

/-- ICARM leaderboard curve 7 has Mordell-Weil rank at least `20`. -/
public theorem curve007_hasRankGE_20 : HasRankGE curve007 20 := by
  unfold curve007
  certify_curve torsion 23 "data/curve007.txt" "data/curve007-labels.txt"

/-- Curve 7 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve007.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 7. -/
public theorem curve007_j : curve007.j = -8860058038489051327873505830623232453040740421940383732399828276783671172005754085165404926579435178209 / 6358347962741427332351207823555533236599280133229903044072065747055673142684922784840133195530240000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
