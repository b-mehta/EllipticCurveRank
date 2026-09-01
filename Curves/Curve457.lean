/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 457 has rank at least 20

The elliptic curve recorded as
[curve 457](https://elliptic-rank.icarm.cloud/curve/457) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² = x³ + x² + a₄·x + a₆`,   with
  `a₄ = -274772680388272620238822915925029108`   and
  `a₆ = 55109431017839872572667629268320431851587994748732288`

over `ℚ`. It has Mordell-Weil rank at least `20`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 457 over `ℚ`. -/
@[expose] public def curve457 : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, -274772680388272620238822915925029108,
    55109431017839872572667629268320431851587994748732288⟩

/-- ICARM leaderboard curve 457 has Mordell-Weil rank at least `20`. -/
public theorem curve457_hasRankGE_20 : HasRankGE curve457 20 := by
  unfold curve457
  certify_curve torsion 47 "data/curve457.txt" "data/curve457-labels.txt"

/-- Curve 457 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve457.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 457. -/
public theorem curve457_j : curve457.j = 238886832259013666329687098593632401237009387977854275702293421864265908993475021850820424740441717712 / 1634393133326384192522367146090628790990926936127026942276916579274364563743733307959844546824529 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
