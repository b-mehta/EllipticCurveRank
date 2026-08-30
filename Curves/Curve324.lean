/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 324 has rank at least 18

The elliptic curve recorded as
[curve 324](https://elliptic-rank.icarm.cloud/curve/324) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy + y = x³ + a₄·x + a₆`,   with
  `a₄ = -10006641313567584974778494`   and
  `a₆ = 12262133853164892979587951115335032676`

over `ℚ`. It has Mordell-Weil rank at least `18`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 324 over `ℚ`. -/
@[expose] public def curve324 : WeierstrassCurve ℚ :=
  ⟨1, 0, 1, -10006641313567584974778494, 12262133853164892979587951115335032676⟩

/-- ICARM leaderboard curve 324 has Mordell-Weil rank at least `18`. -/
public theorem curve324_hasRankGE_18 : HasRankGE curve324 18 := by
  unfold curve324
  certify_curve torsion 37 "data/curve324.txt" "data/curve324-labels.txt"

/-- Curve 324 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve324.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 324. -/
public theorem curve324_j : curve324.j = -3879853268933444053891150158690472842334572210199062153047673539945996595529 / 28986743484558431194750287524549274861356418077344360765954063541056900 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
