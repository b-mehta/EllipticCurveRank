/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under the GNU General Public License version 3.0 as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import ECCompute.Tactic.CertifyCurve
public import ECCompute.Soundness.JInvariant

/-!
# Curve 416 has rank at least 27

The elliptic curve recorded as
[curve 416](https://elliptic-rank.icarm.cloud/curve/416) on the ICARM Elliptic Curve Rank
Leaderboard is

  `E : y² + xy = x³ + a₄·x + a₆`,   with
  `a₄ = -280245422569286389673485906779759546676443623212141473025`   and
  `a₆ = 1766436728610859597051807326576217018574447760859287591309968524822782669465`
  `     597775625`

over `ℚ`. It has Mordell-Weil rank at least `27`. Submitted to the leaderboard by 7fff-zip.
-/

namespace ECCompute

open WeierstrassCurve

/-- ICARM leaderboard curve 416 over `ℚ`. -/
@[expose] public def curve416 : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -280245422569286389673485906779759546676443623212141473025,
    1766436728610859597051807326576217018574447760859287591309968524822782669465597775625⟩

/-- ICARM leaderboard curve 416 has Mordell-Weil rank at least `27`. -/
public theorem curve416_hasRankGE_27 : HasRankGE curve416 27 := by
  unfold curve416
  certify_curve torsion 23 "data/curve416.txt" "data/curve416-labels.txt"

/-- Curve 416 is elliptic (nonzero discriminant), so its `j`-invariant is defined. -/
public instance : curve416.IsElliptic := isElliptic_of_Δ_ne_zero (by decide +kernel)

set_option linter.style.longLine false in
/-- The `j`-invariant of curve 416. -/
public theorem curve416_j : curve416.j = 2434104926004291974281248812441730572277697156828208987471138743002157004516397263910334978884057989511594491688969742478599566612498391163002724731866122868376490812901235601 / 60656490490005214501764462674862504178121595585158962155203002008465561213160134917504974026228944875883385236630694301058504432649839906420906710401195422138178816000000 :=
  j_eq_iff.mpr (by decide +kernel)

end ECCompute
