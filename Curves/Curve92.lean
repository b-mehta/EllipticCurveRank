/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 92 has rank at least 20

The elliptic curve recorded as
[curve 92](https://elliptic-rank.icarm.cloud/curve/92) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -4437412060110743641525245114305`   and
  `a₆ = 3586842216822165612930264910099076801587288127`

over `ℚ`. It has Mordell-Weil rank at least `20`. The witness points from the leaderboard,
transported to the integral short model, are in `data/curve92.txt`; descent labels are in
`data/curve92-labels.txt`. The `certify_curve` tactic kernel-checks the resulting certificate.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 92 over `ℚ`. -/
@[expose] public def curve92 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -4437412060110743641525245114305, 3586842216822165612930264910099076801587288127⟩

/-- ICARM leaderboard curve 92 has Mordell-Weil rank at least `20`. -/
public theorem curve92_hasRankGE_20 : HasRankGE curve92 20 := by
  unfold curve92
  certify_curve torsion 37 "data/curve92.txt" "data/curve92-labels.txt"

/-- Curve 92 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve92.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 92. -/
public theorem curve92_j : curve92.j = 115695723089153244393411983067091539639953769814333231626939680215335524416053678709438885201 / 408975954231094937763805023080293669997958297250320146698783408924921869375744000000000 := j_eq_iff.mpr (by decide +kernel)

end ECCompute
