/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 377 has rank at least 23

The elliptic curve recorded as
[curve 377](https://elliptic-rank.icarm.cloud/curve/377) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -54582530786918941306870296700466269980`   and
  `a₆ = 155508120487725564589054990982409349995405123741445623600`

over `ℚ`. It has Mordell-Weil rank at least `23`. Submitted to the leaderboard by wgxli.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 377 over `ℚ`. -/
@[expose] public def curve377 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -54582530786918941306870296700466269980,
    155508120487725564589054990982409349995405123741445623600⟩

/-- ICARM leaderboard curve 377 has Mordell-Weil rank at least `23`. -/
public theorem curve377_hasRankGE_23 : HasRankGE curve377 23 := by
  unfold curve377
  certify_curve torsion 17 "data/curve377.txt" "data/curve377-labels.txt"

/-- Curve 377 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve377.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 377. -/
public theorem curve377_j : curve377.j = -17145993996429135212641572489109473241542610621335582947924144151935478700836284536562469615247548457045456 / 37744782380097514277218982776136465685885790310144603587922266015763857726976168099896069240777921875 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
