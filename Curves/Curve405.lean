/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 405 has rank at least 18

The elliptic curve recorded as
[curve 405](https://elliptic-rank.icarm.cloud/curve/405) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ - x² + a₄·x + a₆`,   with
  `a₄ = -16548893165735762025678539`   and
  `a₆ = 26839119952931669744569431573523699419`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by Bhavik Mehta.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 405 over `ℚ`. -/
@[expose] public def curve405 : WeierstrassCurve ℚ :=
  ⟨1, -1, 1, -16548893165735762025678539, 26839119952931669744569431573523699419⟩

/-- ICARM leaderboard curve 405 has Mordell-Weil rank at least `18`. -/
public theorem curve405_hasRankGE_18 : HasRankGE curve405 18 := by
  unfold curve405
  certify_curve torsion 5 "data/curve405.txt" "data/curve405-labels.txt"

/-- Curve 405 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve405.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 405. -/
public theorem curve405_j : curve405.j = -687548027912766715141260074261588291672976271655271188919538432644635369504617 / 28980585978709066812234587809654339970292295576264056613263806041254150144 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
