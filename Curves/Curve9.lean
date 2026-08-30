/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 9 has rank at least 23

The elliptic curve recorded as
[curve 9](https://elliptic-rank.icarm.cloud/curve/9) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -19252966408674012828065964616418441723`   and
  `a₆ = 32685500727716376257923347071452044295907443056345614006`

over `ℚ`. It has Mordell-Weil rank at least `23`.

Submitted to the leaderboard by David Renshaw.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 9, a Martin-McMillen rank-23 curve over `ℚ`. -/
@[expose] public def curve9 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -19252966408674012828065964616418441723,
    32685500727716376257923347071452044295907443056345614006⟩

/-- ICARM leaderboard curve 9 has Mordell-Weil rank at least `23`. -/
public theorem curve9_hasRankGE_23 : HasRankGE curve9 23 := by
  unfold curve9
  certify_curve torsion 29 "data/curve9.txt" "data/curve9-labels.txt"

/-- Curve 9 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve9.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 9. -/
public theorem curve9_j : curve9.j = -789253781591678693824973739846986611073718133772361468804106481943172043538173852036304088231525246993289334981987241 / 4779639209650129827198370598581502977994781114856713955972654268540889198350896060545934759063721850651300750000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
