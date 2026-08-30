/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 312 has rank at least 15

The elliptic curve recorded as
[curve 312](https://elliptic-rank.icarm.cloud/curve/312) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -6568019580778599489585141337989692763602574718655`   and
  `a₆ = 6357048702469147640200079650140599226292653501480652916481851397620447847`

over `ℚ`. It has Mordell-Weil rank at least `15`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 312 over `ℚ`. -/
@[expose] public def curve312 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -6568019580778599489585141337989692763602574718655,
    6357048702469147640200079650140599226292653501480652916481851397620447847⟩

set_option linter.style.longLine false in
/-- ICARM leaderboard curve 312 has Mordell-Weil rank at least `15`. -/
public theorem curve312_hasRankGE_15 : HasRankGE curve312 15 := by
  unfold curve312
  certify_curve oneTorsion 5242919295722386142041451 11 "data/curve312.txt" "data/curve312-labels.txt"

/-- Curve 312 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve312.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 312. -/
public theorem curve312_j : curve312.j = 102510323371745118594907183909901892780304308669271316267736036322296680112451613253571826020242825507157393976878649328368720252963 / 2210047804093149601165852365406954218789846145616180545895038969403819193492749149764720830803432395722064899167809284105527296 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
